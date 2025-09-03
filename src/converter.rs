use once_cell::sync::Lazy;
use std::{collections::HashMap, fmt};

const SECTION_DELIMITER: char = '/';
const SUB_SECTION_DELIMITER: char = '·';

const OMISSION_PARTICLE: &str = "[veth]";
const VEILED_PARTICLE: &str = "[selm]";

const MODAL_TRUTH_PARTICLES: [&str; 27] = [
    "[kal]",
    "[kal'mi]",
    "[kal'da]",
    "[ven]",
    "[ven'mi]",
    "[ven'da]",
    "[dūl]",
    "[dūl'mi]",
    "[dūl'da]",
    "[inther'kael]",
    "[inther'kal'mi]",
    "[inther'kal'da]",
    "[na'kal]",
    "[na'kal'mi]",
    "[na'kal'da]",
    "[sarn]",
    "[sarn'mi]",
    "[sarn'da]",
    "[soth]",
    "[soth'mi]",
    "[soth'da]",
    "[vesh]",
    "[vesh'mi]",
    "[vesh'da]",
    "[thur]",
    "[thur'mi]",
    "[thur'da]",
];

static DIGIT_TO_NUMERAL: Lazy<HashMap<char, &'static str>> = Lazy::new(|| {
    HashMap::from([
        ('0', "nil"),
        ('1', "ath"),
        ('2', "bed"),
        ('3', "ken"),
        ('4', "seth"),
        ('5', "saren"),
        ('6', "thae"),
        ('7', "ven"),
        ('8', "rhyl"),
        ('9', "thaen"),
        ('a', "jen"),
        ('b', "maren"),
        ('c', "kaen"),
        ('d', "dol"),
        ('e', "sel"),
        ('f', "eph"),
    ])
});

pub struct Converter {}

impl Converter {
    pub fn to_lothar(input: &str) -> ParseResult<String> {
        // Placeholder implementation
        Ok(input.to_string())
    }

    pub fn from_lothar(input: &str) -> ParseResult<String> {
        // Placeholder implementation
        Ok(input.to_string())
    }
}

impl Converter {
    pub fn new() -> Self {
        Converter {}
    }
}

pub struct NotationParser {}

impl NotationParser {
    pub fn parse(input: &str) -> ParseResult<String> {
        // First step, we can strip all the spaces from the input string.
        let stripped = input.replace(' ', "").to_lowercase();

        // Next, split the string into segments by the '/' character.
        let segments: Vec<&str> = stripped.split(SECTION_DELIMITER).collect();
        if segments.len() != 7 {
            return Err(ParseError::SegmentCountMismatch(segments.len()));
        }

        let mut lothar = String::new();

        // Now we can handle the parsing of the individual segments.
        let date = NotationParser::parse_date(segments[0])?;
        lothar.push_str(&date);
        lothar.push_str(" /\n");

        let time = NotationParser::parse_time(segments[1])?;
        lothar.push_str(&time);
        lothar.push_str(" /\n");

        let location = NotationParser::parse_location(segments[2])?;
        let dimensional_tier = NotationParser::parse_dimensional_tier(segments[3])?;
        let metaphysical_fold = NotationParser::parse_metaphysical_fold(segments[4])?;
        let timeline_branch = NotationParser::parse_timeline_branch(segments[5])?;
        let modal_truth = NotationParser::parse_modal_truth(segments[6])?;

        Ok(lothar)
    }

    fn parse_date(segment: &str) -> ParseResult<String> {
        // In the case of an omission, we can return the segment as is.
        if segment == OMISSION_PARTICLE {
            return Ok(segment.to_string());
        }

        // There should be three sub-segments separated by '·'.
        let sub_segments: Vec<&str> = segment.split(SUB_SECTION_DELIMITER).collect();
        if sub_segments.len() != 4 {
            return Err(ParseError::SubSegmentCountMismatch(3, sub_segments.len()));
        }

        let mut bits = vec![];

        // Iterate through each sub-segment and validate.
        // Each should be a valid hexadecimal number, an omitted particle, or a veiled particle.
        for sub in sub_segments {
            if sub == OMISSION_PARTICLE || sub == VEILED_PARTICLE {
                bits.push(sub.to_string());
            } else if NotationParser::is_valid_hex(sub) {
                bits.push(NotationParser::digit_to_lothar(sub).to_string());
            } else {
                return Err(ParseError::InvalidHexToken(sub.to_string()));
            }
        }

        // Placeholder implementation for date parsing.
        Ok(bits.join(" "))
    }

    fn parse_time(segment: &str) -> ParseResult<String> {
        // In the case of an omission, we can return the segment as is.
        if segment == OMISSION_PARTICLE {
            return Ok(segment.to_string());
        }

        let mut output = String::new();

        // Placeholder implementation for time parsing.
        Ok(output)
    }

    fn parse_location(segment: &str) -> ParseResult<&str> {
        // In the case of an omission, we can return the segment as is.
        if segment == OMISSION_PARTICLE {
            return Ok(segment);
        }

        // Placeholder implementation for location parsing.
        Ok(segment)
    }

    fn parse_dimensional_tier(segment: &str) -> ParseResult<&str> {
        // In the case of an omission, we can return the segment as is.
        if segment == OMISSION_PARTICLE {
            return Ok(segment);
        }

        // Placeholder implementation for dimensional tier parsing.
        Ok(segment)
    }

    fn parse_metaphysical_fold(segment: &str) -> ParseResult<&str> {
        // In the case of an omission, we can return the segment as is.
        if segment == OMISSION_PARTICLE {
            return Ok(segment);
        }

        // Placeholder implementation for metaphysical fold parsing.
        Ok(segment)
    }

    fn parse_timeline_branch(segment: &str) -> ParseResult<&str> {
        // In the case of an omission, we can return the segment as is.
        if segment == OMISSION_PARTICLE {
            return Ok(segment);
        }

        // Placeholder implementation for timeline branch parsing.
        Ok(segment)
    }

    fn parse_modal_truth(segment: &str) -> ParseResult<&str> {
        // The modal truth segment may not be omitted or veiled, under any circumstance.

        // Placeholder implementation for modal truth parsing.
        Ok(segment)
    }

    fn digit_to_lothar(s: &str) -> String {
        let mut bits = vec![];

        for c in s.chars() {
            if let Some(&digit) = DIGIT_TO_NUMERAL.get(&c) {
                bits.push(digit);
            } else {
                // If we encounter an invalid character, we can choose to handle it.
                // For now, we'll just append the character as is.
                bits.push("?");
            }
        }

        bits.join("'").to_string()
    }

    fn is_valid_hex(s: &str) -> bool {
        // Empty string should probably be considered invalid.
        if s.is_empty() {
            return false;
        }

        u64::from_str_radix(s, 16).is_ok()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    SegmentCountMismatch(usize),
    SubSegmentCountMismatch(usize, usize),
    InvalidHexToken(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::SegmentCountMismatch(count) => {
                write!(f, "Segment count incorrect, expected 7, got {count}")
            }
            ParseError::SubSegmentCountMismatch(expected, count) => {
                write!(
                    f,
                    "Sub-segment count incorrect, expected {expected}, got {count}"
                )
            }
            ParseError::InvalidHexToken(token) => {
                write!(f, "Invalid hexadecimal token: '{token}'")
            }
        }
    }
}

impl std::error::Error for ParseError {}

type ParseResult<T> = Result<T, ParseError>;

#[cfg(test)]
mod tests {
    use super::*;

    struct TestEntry<'a> {
        input: &'static str,
        expected: ParseResult<&'a str>,
    }

    #[test]
    fn test_notation_segment_parser() {
        let tests = vec![
            // Omitted date segment, everything else is defined.
            TestEntry {
                input: "[veth] / E·23·34·1 / 9·2·A / C3 / A1 / B99D / [kal'mi]",
                expected: Ok("[veth] /\n /\n"),
            },
            // Omitted time segment, everything else is defined.
            TestEntry {
                input: "12BFF·7·D·5 / [veth] / 9·2·A / C3 / A1 / B99D / [kal'mi]",
                expected: Ok("ath'bed'maren'eph'eph ven dol saren /\n[veth] /\n"),
            },
        ];

        for (i, test) in tests.iter().enumerate() {
            let result = NotationParser::parse(test.input);
            if result.is_err() && test.expected.is_err() {
                continue; // Both are errors, the test passes.
            }

            match (&result, &test.expected) {
                (Ok(r1), Ok(r2)) => assert_eq!(
                    r1, r2,
                    "Test case {i} failed: result '{r1}' != expected '{r2}'"
                ),
                (Err(e1), Err(e2)) => assert_eq!(
                    e1, e2,
                    "Test case {i} failed: result '{e1}' != expected '{e2}'"
                ),
                _ => assert!(
                    false,
                    "Test case {i} failed: mismatched result and expected: '{result:?}' != '{:?}'",
                    test.expected
                ),
            }
        }
    }
}
