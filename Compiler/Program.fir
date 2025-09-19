## Defines the program-level state: package and module database.


import [Compiler/Defs]


type Program(
    _modules: Vec[Module],
)


Program.loadModule(self, path: Vec[Str]) ModuleIdx:
    panic("TODO")
