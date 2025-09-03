mod converter;

use crate::converter::NotationParser;

fn main() {
    let result = NotationParser::parse("[veth] / E·23·34·1 / 9·2·A / C3 / A1 / B99D / [kal'mi]");
    println!("{result:?}");
}
