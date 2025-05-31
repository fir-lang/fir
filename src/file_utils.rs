pub fn extract_text(contents: &str, start: (usize, usize), end: (usize, usize)) -> Option<String> {
    let lines: Vec<&str> = contents.lines().collect();

    if start.0 > end.0 || start.0 >= lines.len() || end.0 >= lines.len() {
        return None;
    }

    if start.0 == end.0 {
        let line = lines[start.0];
        if start.1 > line.len() || end.1 > line.len() || start.1 > end.1 {
            return None;
        }
        return Some(line[start.1..end.1].to_string());
    }

    let mut result = String::new();

    let first_line = lines[start.0];
    if start.1 > first_line.len() {
        return None;
    }
    result.push_str(&first_line[start.1..]);
    result.push('\n');

    for line_idx in (start.0 + 1)..end.0 {
        result.push_str(lines[line_idx]);
        result.push('\n');
    }

    let last_line = lines[end.0];
    if end.1 > last_line.len() {
        return None;
    }
    result.push_str(&last_line[..end.1]);

    Some(result)
}
