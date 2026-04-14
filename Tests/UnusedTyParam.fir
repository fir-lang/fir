# Not sure if we want to support unused type parameters.. for now this works and
# we don't want to break this *accidentally*, only deliberately.

test[ToStr[t]](): printStr("Hi")

main(): ()
