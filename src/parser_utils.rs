pub(crate) fn parse_char_lit(text: &str) -> char {
    let mut chars = text.chars();

    let quote = chars.next(); // skip '
    debug_assert_eq!(quote, Some('\''));

    let char = chars.next().unwrap();
    if char == '\\' {
        match chars.next().unwrap() {
            '\'' => '\'',
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            '\\' => '\\',
            other => panic!("Unknown escaped character: '\\{}'", other),
        }
    } else {
        char
    }
}
