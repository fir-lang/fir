type HashMap[k, v](Vec[Option[Elem[k, v]]])

type HashMap[k, v](Vec[Option[Elem[k, v]]],)

type HashMap[k, v](
    fields: Vec[Option[Elem[k, v]]]
)

type HashMap[k, v](
    fields: Vec[Option[Elem[k, v]]],
)

# expected stdout:
# type HashMap[k, v](Vec[Option[Elem[k, v]]])
# 
# 
# type HashMap[k, v](Vec[Option[Elem[k, v]]],)
# 
# 
# type HashMap[k, v](
#     fields: Vec[Option[Elem[k, v]]],
# )
# 
# 
# type HashMap[k, v](
#     fields: Vec[Option[Elem[k, v]]],
# )
