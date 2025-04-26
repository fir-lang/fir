main
    let \
    vec \
    : \
                Vec[U32] \
= \
            Vec \
. \
        withCapacity(10)

    vec \
    . \
    push \
    (1u32)

    for \
    x \
        : \
        U32 \
in \
vec \
        . \
    iter():
        ()
