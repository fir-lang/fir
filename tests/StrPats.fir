main():
    match "test":
        "asdf": panic("")
        "test": printStr("OK")
        _: panic("")

# expected stdout:
# OK
