use crate::ast;
use crate::collections::*;
use crate::module::ModulePath;
use crate::name::Name;
use crate::utils::loc_display;

use std::fmt;
use std::path::Path;

use smol_str::SmolStr;

/// An import of a single module.
#[derive(Debug, Clone)]
pub struct ModuleImport {
    pub path: ModulePath,
    pub kind: ImportKind,
}

#[derive(Debug, Clone)]
pub enum ImportKind {
    /// Import into the flat namespace: everything (filter = `None`) or selectively with optional
    /// renaming (filter = `Some(map)`). Keys are original names, values are local names.
    Direct { filter: Option<HashMap<Name, Name>> },

    /// Import everything under a prefix: `import [Foo as P]` makes names available as `P/name`.
    Prefixed { prefix: Name },
}

#[derive(Debug)]
pub struct LoadedPgm {
    pub modules: HashMap<ModulePath, ast::Module>,

    pub entry: ModulePath,

    /// Maps modules to modules they import.
    pub dep_graph: HashMap<ModulePath, Vec<ModuleImport>>,

    pub scc_graph: SccGraph,
}

/// DAG of strongly connected components.
#[derive(Debug)]
pub struct SccGraph {
    /// SCCs, topologically sorted.
    pub nodes: Vec<SccNode>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SccIdx(usize);

impl SccIdx {
    pub fn as_usize(self) -> usize {
        self.0
    }
}

/// A strongly connected component of modules.
#[derive(Debug)]
pub struct SccNode {
    /// Modules in this SCC.
    pub modules: Vec<ModulePath>,

    /// Indices into `SccGraph::nodes` of SCCs that depend on this one.
    pub dependents: Vec<SccIdx>,

    /// Indices into `SccGraph::nodes` of SCCs that this one depends on.
    #[allow(unused)]
    pub dependencies: Vec<SccIdx>,
}

pub fn load(entry_file: &Path, print_parsed_ast: bool, test_ast_printer: bool) -> LoadedPgm {
    let entry = ModulePath::from_file_path(entry_file);
    let mut work: Vec<ModulePath> = vec![entry.clone()];
    let mut modules: HashMap<ModulePath, ast::Module> = HashMap::default();
    modules.insert(entry.clone(), ast::Module::empty());

    let mut dep_graph: HashMap<ModulePath, Vec<ModuleImport>> = Default::default();

    let prelude_path = ModulePath::new(vec![
        SmolStr::new_static("Fir"),
        SmolStr::new_static("Prelude"),
    ]);

    while let Some(module_path) = work.pop() {
        let file_path = module_path.to_file_path();
        let display_name = module_path.to_string();
        let module = crate::parse_file(
            &file_path,
            &display_name,
            print_parsed_ast,
            test_ast_printer,
        );

        dep_graph.entry(module_path.clone()).or_default();

        let mut implicit_prelude = true;

        for decl in &module.decls {
            if let ast::TopDecl::Import(import) = &decl.node {
                implicit_prelude &= !no_implicit_prelude(import);
                for item in &import.node.items {
                    if !modules.contains_key(&item.path) {
                        modules.insert(item.path.clone(), ast::Module::empty());
                        work.push(item.path.clone());
                    }
                    let kind = match &item.import_spec {
                        Some(ast::ImportSpec::Selective { names }) => ImportKind::Direct {
                            filter: Some(
                                names
                                    .iter()
                                    .map(|n| {
                                        (Name::from(&n.original_name), Name::from(&n.local_name))
                                    })
                                    .collect(),
                            ),
                        },
                        Some(ast::ImportSpec::Prefixed { prefix }) => ImportKind::Prefixed {
                            prefix: Name::from(prefix),
                        },
                        None => ImportKind::Direct { filter: None },
                    };
                    dep_graph.get_mut(&module_path).unwrap().push(ModuleImport {
                        path: item.path.clone(),
                        kind,
                    });
                }
            }
        }

        if module_path != prelude_path && implicit_prelude {
            if !modules.contains_key(&prelude_path) {
                modules.insert(prelude_path.clone(), ast::Module::empty());
                work.push(prelude_path.clone());
            }
            dep_graph.get_mut(&module_path).unwrap().push(ModuleImport {
                path: prelude_path.clone(),
                kind: ImportKind::Direct { filter: None },
            });
        }

        let old = modules.insert(module_path, module);
        debug_assert!(old.unwrap().decls.is_empty());
    }

    let scc_graph = build_scc_graph(&dep_graph);
    // println!("{scc_graph}");

    LoadedPgm {
        modules,
        entry,
        dep_graph,
        scc_graph,
    }
}

impl LoadedPgm {
    pub fn iter_decls(&self) -> impl Iterator<Item = (&ModulePath, &ast::L<ast::TopDecl>)> {
        self.modules
            .iter()
            .flat_map(|(path, module)| module.decls.iter().map(move |decl| (path, decl)))
    }

    pub fn iter_decls_mut(
        &mut self,
    ) -> impl Iterator<Item = (&ModulePath, &mut ast::L<ast::TopDecl>)> {
        self.modules
            .iter_mut()
            .flat_map(|(path, module)| module.decls.iter_mut().map(move |decl| (path, decl)))
    }

    pub fn print(&self) {
        for (i, (module_path, module)) in self.modules.iter().enumerate() {
            if i != 0 {
                println!();
            }
            println!("mod {} {{\n", module_path);
            module.print();
            println!("\n}} # {}", module_path);
        }
    }
}

fn build_scc_graph(graph: &HashMap<ModulePath, Vec<ModuleImport>>) -> SccGraph {
    let graph: HashMap<ModulePath, HashSet<ModulePath>> = graph
        .iter()
        .map(|(k, imports)| (k.clone(), imports.iter().map(|i| i.path.clone()).collect()))
        .collect();

    let sccs = scc(&graph);

    // Map each module to its SCC index.
    let mut module_to_scc: HashMap<ModulePath, SccIdx> = HashMap::default();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for module in scc {
            module_to_scc.insert(module.clone(), SccIdx(scc_idx));
        }
    }

    let num_sccs = sccs.len();
    let mut dependents: Vec<HashSet<SccIdx>> = vec![HashSet::default(); num_sccs];
    let mut dependencies: Vec<HashSet<SccIdx>> = vec![HashSet::default(); num_sccs];

    for (u, deps) in &graph {
        let u_scc = module_to_scc[u];
        for v in deps {
            let v_scc = module_to_scc[v];
            if u_scc != v_scc {
                // SCC u depends on SCC v
                dependents[v_scc.as_usize()].insert(u_scc);
                dependencies[u_scc.as_usize()].insert(v_scc);
            }
        }
    }

    let nodes = sccs
        .into_iter()
        .enumerate()
        .map(|(i, modules)| SccNode {
            modules,
            dependents: dependents[i].iter().copied().collect(),
            dependencies: dependencies[i].iter().copied().collect(),
        })
        .collect();

    SccGraph { nodes }
}

fn scc(graph: &HashMap<ModulePath, HashSet<ModulePath>>) -> Vec<Vec<ModulePath>> {
    let mut all_nodes: HashSet<ModulePath> = HashSet::default();
    for (node, deps) in graph {
        all_nodes.insert(node.clone());
        for dep in deps {
            all_nodes.insert(dep.clone());
        }
    }

    struct State {
        index_counter: u32,
        stack: Vec<ModulePath>,
        on_stack: HashSet<ModulePath>,
        index: HashMap<ModulePath, u32>,
        lowlink: HashMap<ModulePath, u32>,
        result: Vec<Vec<ModulePath>>,
    }

    fn strongconnect(
        v: &ModulePath,
        graph: &HashMap<ModulePath, HashSet<ModulePath>>,
        state: &mut State,
    ) {
        let idx = state.index_counter;
        state.index_counter += 1;
        state.index.insert(v.clone(), idx);
        state.lowlink.insert(v.clone(), idx);
        state.stack.push(v.clone());
        state.on_stack.insert(v.clone());

        if let Some(deps) = graph.get(v) {
            for w in deps {
                if !state.index.contains_key(w) {
                    strongconnect(w, graph, state);
                    let w_lowlink = state.lowlink[w];
                    let v_lowlink = state.lowlink.get_mut(v).unwrap();
                    *v_lowlink = (*v_lowlink).min(w_lowlink);
                } else if state.on_stack.contains(w) {
                    let w_index = state.index[w];
                    let v_lowlink = state.lowlink.get_mut(v).unwrap();
                    *v_lowlink = (*v_lowlink).min(w_index);
                }
            }
        }

        if state.lowlink[v] == state.index[v] {
            let mut scc = Vec::new();
            loop {
                let w = state.stack.pop().unwrap();
                state.on_stack.remove(&w);
                let done = w == *v;
                scc.push(w);
                if done {
                    break;
                }
            }
            state.result.push(scc);
        }
    }

    let mut state = State {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::default(),
        index: HashMap::default(),
        lowlink: HashMap::default(),
        result: Vec::new(),
    };

    for node in &all_nodes {
        if !state.index.contains_key(node) {
            strongconnect(node, graph, &mut state);
        }
    }

    state.result
}

fn no_implicit_prelude(import: &ast::L<ast::ImportDecl>) -> bool {
    for attr in import.node.attrs.iter() {
        if attr.lhs.is_some() {
            continue;
        }
        let attr = &attr.expr.node;
        if let ast::Expr::ConSel(ast::Con {
            mod_prefix: _,
            ty,
            con,
            ty_user_ty_args: user_ty_args,
            ..
        }) = attr
            && ty == &ast::Name::new_static("NoImplicitPrelude")
            && con.is_none()
            && user_ty_args.is_empty()
        {
            return true;
        }
        panic!(
            "{}: Weird `import` attribute: {}",
            loc_display(&import.loc),
            attr
        );
    }
    false
}

impl fmt::Display for SccIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for SccIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for SccGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, node) in self.nodes.iter().enumerate() {
            if i != 0 {
                writeln!(f)?;
            }

            write!(f, "SCC {}: ", i)?;

            write!(f, "{{")?;
            for (j, m) in node.modules.iter().enumerate() {
                if j != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", m)?;
            }
            write!(f, "}}")?;

            let mut dependents = node.dependents.clone();
            dependents.sort();

            let mut dependencies = node.dependencies.clone();
            dependencies.sort();

            write!(
                f,
                " dependents={:?} dependencies={:?}",
                dependents, dependencies
            )?;
        }
        Ok(())
    }
}
