# Not sure if we want to support unused type parameters.. for now this works and
# we don't want to break this *accidentally*, only deliberately.

fn test1[t: ToStr]() = printStr("Hi")

fn test2[t]() = printStr("Hi")

fn main() = ()
