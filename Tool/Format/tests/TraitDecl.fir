trait Iterator[iter, item, exn]:
    next(self: iter) Option[item] / exn

    map(self: iter, f: Fn(item) b / exn) Map[iter, item, b, exn]

    peekable(self: iter) Peekable[iter, item, exn]

# expected stdout:
# trait Iterator[iter, item, exn]:
#     next(self: iter) Option[item] / exn
# 
#     map(self: iter, f: Fn(item) b / exn) Map[iter, item, b, exn]
# 
#     peekable(self: iter) Peekable[iter, item, exn]
