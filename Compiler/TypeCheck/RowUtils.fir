import [
    Compiler/Assert,
    Compiler/TypeCheck/Ty,
]


collectRows(
    ty: Ty,
    tyKind: RecordOrVariant,
    labels: HashMap[LocalId, Ty],
    extension: Option[Ty],
) (rows: HashMap[LocalId, Ty], extension: Option[Ty]):
    let allLabels: HashMap[LocalId, Ty] = HashMap.fromIter(
        labels.iter().map(
            \(label: HashMapEntry[LocalId, Ty]):
                (key = label.key, value = label.value.deepNormalize()),
        ),
    )

    while extension is Option.Some(ext):
        match ext:
            Ty.Anonymous(labels, extension = nextExt, kind, isRow):
                assert(kind == tyKind)
                assert(isRow)
                for label: HashMapEntry[LocalId, Ty] in labels.iter():
                    if allLabels.insert(label.key, label.value)
                            is Option.Some(_):
                        panic(
                            "BUG: Duplicate label in anonymous type `ty.toDoc().render(50)`",
                        )
                extension = nextExt

            Ty.UVar(uvar):
                assert(uvar.kind is Kind.Row(_))
                match uvar.normalize():
                    Ty.Anonymous(labels, extension = nextExt, kind, isRow):
                        assert(isRow)
                        assert(kind == tyKind)
                        for label: HashMapEntry[LocalId, Ty] in labels.iter():
                            if allLabels.insert(label.key, label.value)
                                    is Option.Some(_):
                                panic(
                                    "BUG: Duplicate label in anonymous type `ty.toDoc().render(50)`",
                                )
                        extension = nextExt

                    other:
                        return (
                            rows = allLabels, extension = Option.Some(other)
                        )

            other: return (rows = allLabels, extension = Option.Some(other))

    (rows = allLabels, extension = Option.None)
