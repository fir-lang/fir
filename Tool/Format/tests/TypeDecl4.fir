#|1|#
type #|2|# Foo #|3|# = #|4|# U32 #|5|#

type Foo #|6|# [ #|7|# t #|8|# , #|9|# ] #|10|# = #|11|# Vec[t] #|12|#

type Foo = U32

type Foo[t] = Vec[t]

# expected stdout:
# #|1|#
# type #|2|#  Foo #|3|#  = #|4|#  U32 #|5|# 
# 
# 
# type Foo #|6|# [ #|7|# t #|8|# , #|9|# ] #|10|#  = #|11|#  Vec[t] #|12|# 
# 
# 
# type Foo = U32
# 
# 
# type Foo[t] = Vec[t]
