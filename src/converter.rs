use once_cell::sync::Lazy;
use std::{collections::HashMap, fmt};

/// The character used to separate the main sections of a notation string.
const SECTION_DELIMITER: char = '/';
/// The character used to separate sub-sections within a main section.
const SUB_SECTION_DELIMITER: char = '·';

/// The particle used to indicate an omitted segment.
const OMISSION_PARTICLE: &str = "[veth]";

/// The particle used to indicate a veiled segment or sub-segment.
const VEILED_PARTICLE: &str = "[selm]";

/// The valid modal truth particles.
const MODAL_TRUTH_PARTICLES: [&str; 48] = [
    // "is true"
    "[kal]",
    "[kal'mi]",
    "[kal'da]",
    // "is not true"
    "[na'kal]",
    "[na'kal'mi]",
    "[na'kal'da]",
    // "will be true"
    "[ven]",
    "[ven'mi]",
    "[ven'da]",
    // "will not be true"
    "[na'ven]",
    "[na'ven'mi]",
    "[na'ven'da]",
    // "was once true"
    "[dūl]",
    "[dūl'mi]",
    "[dūl'da]",
    // "was not once true"
    "[na'dūl]",
    "[na'dūl'mi]",
    "[na'dūl'da]",
    // "true before the origin [of all]"
    "[inther'kael]",
    "[inther'kal'mi]",
    "[inther'kal'da]",
    // "not true before the origin [of all]"
    "[na'inther'kael]",
    "[na'inther'kal'mi]",
    "[na'inther'kal'da]",
    // "forbidden, but metaphysically true"
    "[sarn]",
    "[sarn'mi]",
    "[sarn'da]",
    // "forbidden, but not metaphysically true"
    "[na'sarn]",
    "[na'sarn'mi]",
    "[na'sarn'da]",
    // "indeterminate" or "currently unknowable"
    "[soth]",
    "[soth'mi]",
    "[soth'da]",
    // "not currently unknowable"
    "[na'soth]",
    "[na'soth'mi]",
    "[na'soth'da]",
    // "known true, but forbidden to declare"
    "[vesh]",
    "[vesh'mi]",
    "[vesh'da]",
    // "not known true, but forbidden to declare"
    "[na'vesh]",
    "[na'vesh'mi]",
    "[na'vesh'da]",
    // "unknowable truth"
    "[thur]",
    "[thur'mi]",
    "[thur'da]",
    // "not unknowable truth"
    "[na'thur]",
    "[na'thur'mi]",
    "[na'thur'da]",
];

/// Mapping from hexadecimal digit characters to their corresponding Lothar numerals.
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

/// Names of the sub-sections for each main section.
static SUB_SECTION_NAMES: Lazy<Vec<Vec<&str>>> = Lazy::new(|| {
    vec![
        vec!["tharyn", "yen", "kaemar", "theren"],
        vec!["orenth", "mineth", "lunath", "thren"],
        // If you need more than 15 axes... I don't know what to tell you.
        vec![
            "xar", "yar", "zar", "war", "var", "uar", "tar", "sar", "rar", "qar", "par", "oar",
            "nar", "mar", "lar", "kar",
        ],
        vec!["daren"],
        vec!["duul"],
        vec!["voth"],
        vec![],
    ]
});

/// A flattened list of all sub-section names for easy validation.
static ALL_SUB_SECTION_NAMES: Lazy<Vec<&str>> =
    Lazy::new(|| SUB_SECTION_NAMES.iter().flatten().copied().collect());

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
        for (i, &sub) in sub_segments.iter().enumerate() {
            let mut sub_string = String::new();

            // Add the name of the sub-segment.
            sub_string.push_str(SUB_SECTION_NAMES[0][i]);
            sub_string.push_str("'");

            if sub == OMISSION_PARTICLE || sub == VEILED_PARTICLE {
                sub_string.push_str(&NotationParser::strip_square_brackets(sub));
            } else if NotationParser::is_valid_hex(sub) {
                sub_string.push_str(&NotationParser::digit_to_lothar(sub));
            } else {
                return Err(ParseError::InvalidHexToken(sub.to_string()));
            }

            bits.push(sub_string)
        }

        // Placeholder implementation for date parsing.
        Ok(bits.join(" "))
    }

    fn parse_time(segment: &str) -> ParseResult<String> {
        // In the case of an omission, we can return the segment as is.
        if segment == OMISSION_PARTICLE {
            return Ok(segment.to_string());
        }

        let output = String::new();

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

    fn strip_square_brackets(s: &str) -> &str {
        s.trim_start_matches('[').trim_end_matches(']')
    }

    fn digit_to_lothar(s: &str) -> String {
        let mut out = String::new();

        for (i, c) in s.chars().enumerate() {
            if i > 0 {
                out.push('\'');
            }

            out.push_str(DIGIT_TO_NUMERAL.get(&c).copied().unwrap_or("?"));
        }

        out
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
                expected: Ok(
                    "tharyn'ath'bed'maren'eph'eph yen'ven kaemar'dol theren'saren /\n[veth] /\n",
                ),
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
