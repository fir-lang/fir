import [Fir/C as C]


toCSize(i: U32) C/SizeT:
    C/inline("(size_t)`i`")


toU32(i: C/SizeT) U32:
    C/inline("(uint32_t)`i`")


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
    let path = "/tmp/fir_ffi_rw_test\0"
    let w_mode = "w\0"
    let r_mode = "r\0"

    # Write "Hi!" to the file.
    let fw = fopen(path._bytes.ptr(), w_mode._bytes.ptr())
    if fw.isNull():
        panic("fopen for write failed")

    let out = "Hi!"
    let nw = fwrite(out._bytes.ptr(), u32(1).toCSize(), u32(3).toCSize(), fw)
    printStr("wrote `nw.toU32()` bytes")
    let _ = fclose(fw)

    # Read it back.
    let fr = fopen(path._bytes.ptr(), r_mode._bytes.ptr())
    if fr.isNull():
        panic("fopen for read failed")

    let buf: Array[U8] = Array.new(3)
    let nr = fread(buf.ptr(), u32(1).toCSize(), u32(3).toCSize(), fr)
    let _ = fclose(fr)

    printStr("read `nr.toU32()` bytes")
    for i in range(u32(0), nr.toU32()):
        printStr("byte[`i`] = `buf.get(i).asU32()`")


# expected stdout:
# wrote 3 bytes
# read 3 bytes
# byte[0] = 72
# byte[1] = 105
# byte[2] = 33
