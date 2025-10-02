import [Compiler/TypeCheck/Ty,]


collectRows(
    ty: Ty,
    tyKind: RecordOrVariant,
    labels: HashMap[LocalId, Ty],
    extension: Option[Ty],
) (rows: HashMap[LocalId, Ty], extension: Option[Ty]):
    panic("TODO")
