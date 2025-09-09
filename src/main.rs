mod converter;

use crate::converter::NotationParser;

fn main() {
    let mut parser = NotationParser::new();
    let result = parser.parse("12BFF·7·D·5 / E·23·34·1 / 9·2·A / C3 / A1 / B99D / [kal'mi]");
    if let Ok(s) = result {
        println!("{s}");
    } else {
        eprintln!("Error: {result:?}");
    }
}
