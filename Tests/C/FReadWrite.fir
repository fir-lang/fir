import [Fir/C as C]


toCSize(i: U32) C/SizeT:
    C/inline("(size_t)`i`")

toU32(i: C/SizeT) U32:
    C/inline("(uint32_t)`i`")


nullTerminated(bytes: Vec[U8]) Array[U8]:
    bytes.push(0)
    bytes.takeArray()


extern type File = "FILE"


fopen(path: C/Ptr[U8], mode: C/Ptr[U8]) C/Ptr[File]:
    C/inline("fopen((const char*)`path`, (const char*)`mode`)")


fclose(stream: C/Ptr[File]) C/Int:
    C/inline("fclose(`stream`)")


fread(ptr: C/Ptr[U8], size: C/SizeT, nmemb: C/SizeT, stream: C/Ptr[File]) C/SizeT:
    C/inline("fread(`ptr`, `size`, `nmemb`, `stream`)")


fwrite(ptr: C/Ptr[U8], size: C/SizeT, nmemb: C/SizeT, stream: C/Ptr[File]) C/SizeT:
    C/inline("fwrite(`ptr`, `size`, `nmemb`, `stream`)")


main():
    # "/tmp/fir_ffi_rw_test"
    let path_v: Vec[U8] = Vec.[
        u8(47), u8(116), u8(109), u8(112), u8(47),
        u8(102), u8(105), u8(114), u8(95),
        u8(102), u8(102), u8(105), u8(95),
        u8(114), u8(119), u8(95),
        u8(116), u8(101), u8(115), u8(116),
    ]
    let path = nullTerminated(path_v)

    let w_mode_v: Vec[U8] = Vec.[u8(119)] # "w"
    let w_mode = nullTerminated(w_mode_v)

    let r_mode_v: Vec[U8] = Vec.[u8(114)] # "r"
    let r_mode = nullTerminated(r_mode_v)

    # Write "Hi!" to the file.
    let fw = fopen(path.ptr(), w_mode.ptr())
    if fw.isNull():
        panic("fopen for write failed")

    let out: Array[U8] = Array.new(3)
    out.set(u32(0), u8(72))  # H
    out.set(u32(1), u8(105)) # i
    out.set(u32(2), u8(33))  # !
    let nw = fwrite(out.ptr(), u32(1).toCSize(), u32(3).toCSize(), fw)
    printStr("wrote `nw.toU32()` bytes")
    let _ = fclose(fw)

    # Read it back.
    let fr = fopen(path.ptr(), r_mode.ptr())
    if fr.isNull():
        panic("fopen for read failed")

    let buf: Array[U8] = Array.new(3)
    let nr = fread(buf.ptr(), u32(1).toCSize(), u32(3).toCSize(), fr)
    let _ = fclose(fr)

    printStr("read `nr.toU32()` bytes")
    for i: U32 in range(u32(0), nr.toU32()):
        printStr("byte[`i`] = `buf.get(i).asU32()`")


# expected stdout:
# wrote 3 bytes
# read 3 bytes
# byte[0] = 72
# byte[1] = 105
# byte[2] = 33
