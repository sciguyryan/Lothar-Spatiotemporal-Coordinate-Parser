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

/// The names of the segments of the spatiotemporal notation.
const SEGMENT_NAMES: [&str; 7] = [
    "tharyn'kael",
    "lux'kael",
    "xaryen'kael",
    "daren'dur",
    "duul'kael",
    "varyn'dur",
    "sarn'darien",
];

pub struct NotationParser {
    lothar: String,
}

impl NotationParser {
    pub fn new() -> Self {
        NotationParser {
            lothar: String::new(),
        }
    }

    pub fn parse(&mut self, input: &str) -> ParseResult<&String> {
        // First step, we can strip all the spaces from the input string.
        let stripped = input.replace(' ', "").to_lowercase();

        // Next, split the string into segments by the '/' character.
        let segments: Vec<&str> = stripped.split(SECTION_DELIMITER).collect();
        if segments.len() != 7 {
            return Err(ParseError::SegmentCountMismatch(segments.len()));
        }

        // Now we can handle the parsing of the individual segments.
        self.parse_date_segment(segments[0])?;
        self.parse_time_segment(segments[1])?;
        self.parse_location_segment(segments[2])?;
        self.parse_dimensional_tier_segment(segments[3])?;
        self.parse_metaphysical_fold_segment(segments[4])?;
        self.parse_timeline_branch_segment(segments[5])?;
        self.parse_modal_truth_segment(segments[6])?;

        Ok(&self.lothar)
    }

    fn push_segment(&mut self, segment: &str, segment_index: usize) {
        self.lothar.push_str(segment);

        if segment_index < SEGMENT_NAMES.len() - 1 {
            self.lothar.push_str(" /\n");
        }
    }

    fn push_special_particle_segment(&mut self, particle: &str, segment_index: usize) {
        let merged = format!(
            "{}'{}",
            SEGMENT_NAMES[segment_index],
            NotationParser::strip_particle_brackets(particle)
        );

        self.push_segment(&merged, segment_index);
    }

    fn parse_date_segment(&mut self, segment: &str) -> ParseResult<()> {
        // In the case of an omission or veiling, we can push the segment as is.
        if segment == OMISSION_PARTICLE || segment == VEILED_PARTICLE {
            self.push_special_particle_segment(segment, 0);
            return Ok(());
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
                sub_string.push_str(&NotationParser::strip_particle_brackets(sub));
            } else if NotationParser::is_valid_hex(sub) {
                sub_string.push_str(&NotationParser::digit_to_lothar(sub)?);
            } else {
                return Err(ParseError::InvalidHexToken(sub.to_string()));
            }

            bits.push(sub_string)
        }

        self.push_segment(&bits.join(" "), 0);
        Ok(())
    }

    fn parse_time_segment(&mut self, segment: &str) -> ParseResult<()> {
        // In the case of an omission or veiling, we can push the segment as is.
        if segment == OMISSION_PARTICLE || segment == VEILED_PARTICLE {
            self.push_special_particle_segment(segment, 1);
            return Ok(());
        }

        // Placeholder implementation for time segment parsing.
        let output = String::new();

        self.push_segment(&output, 1);
        Ok(())
    }

    fn parse_location_segment(&mut self, segment: &str) -> ParseResult<()> {
        // In the case of an omission or veiling, we can push the segment as is.
        if segment == OMISSION_PARTICLE || segment == VEILED_PARTICLE {
            self.push_special_particle_segment(segment, 2);
            return Ok(());
        }

        // Placeholder implementation for location segment parsing.
        let output = String::new();

        self.push_segment(&output, 2);
        Ok(())
    }

    fn parse_dimensional_tier_segment(&mut self, segment: &str) -> ParseResult<()> {
        // In the case of an omission or veiling, we can push the segment as is.
        if segment == OMISSION_PARTICLE || segment == VEILED_PARTICLE {
            self.push_special_particle_segment(segment, 3);
            return Ok(());
        }

        // Placeholder implementation for dimensional tier segment parsing.
        let output = String::new();

        self.push_segment(&output, 3);
        Ok(())
    }

    fn parse_metaphysical_fold_segment(&mut self, segment: &str) -> ParseResult<()> {
        // In the case of an omission or veiling, we can push the segment as is.
        if segment == OMISSION_PARTICLE || segment == VEILED_PARTICLE {
            self.push_special_particle_segment(segment, 4);
            return Ok(());
        }

        // Placeholder implementation for metaphysical fold segment parsing.
        let output = String::new();

        self.push_segment(&output, 4);
        Ok(())
    }

    fn parse_timeline_branch_segment(&mut self, segment: &str) -> ParseResult<()> {
        // In the case of an omission or veiling, we can push the segment as is.
        if segment == OMISSION_PARTICLE || segment == VEILED_PARTICLE {
            self.push_special_particle_segment(segment, 5);
            return Ok(());
        }

        // Placeholder implementation for timeline branch segment parsing.
        let output = String::new();

        self.push_segment(&output, 5);
        Ok(())
    }

    fn parse_modal_truth_segment(&mut self, segment: &str) -> ParseResult<()> {
        // The modal truth segment may not be omitted or veiled, under any circumstance
        // as it serves as the anchor between the speaker and the entire coordinate.
        if segment == OMISSION_PARTICLE || segment == VEILED_PARTICLE {
            return Err(ParseError::ModalTruthOmission);
        }

        // The modal truth particle must be one of the defined valid particles.
        if MODAL_TRUTH_PARTICLES.contains(&segment) {
            self.push_segment(NotationParser::strip_particle_brackets(segment), 6);
            Ok(())
        } else {
            Err(ParseError::InvalidModalTruthParticle(segment.to_string()))
        }
    }

    fn strip_particle_brackets(s: &str) -> &str {
        s.trim_start_matches('[').trim_end_matches(']')
    }

    fn digit_to_lothar(s: &str) -> ParseResult<String> {
        let mut out = String::new();

        for (i, c) in s.chars().enumerate() {
            if i > 0 {
                out.push('\'');
            }

            if let Some(digit) = DIGIT_TO_NUMERAL.get(&c) {
                out.push_str(digit);
            } else {
                return Err(ParseError::InvalidHexToken(s.to_string()));
            }
        }

        Ok(out)
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
    ModalTruthOmission,
    InvalidModalTruthParticle(String),
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
            ParseError::ModalTruthOmission => {
                write!(f, "Modal truth segment cannot be omitted")
            }
            ParseError::InvalidModalTruthParticle(particle) => {
                write!(f, "Invalid modal truth particle: '{particle}'")
            }
        }
    }
}

impl std::error::Error for ParseError {}

type ParseResult<T> = Result<T, ParseError>;

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf};

    use super::*;

    struct TestEntry {
        id: usize,
        input: String,
        output: String,
        expected: ParseResult<()>,
    }

    impl TestEntry {
        fn new(
            id: usize,
            input_file: &str,
            expected_file: &str,
            expected: ParseResult<()>,
        ) -> Self {
            Self {
                id,
                input: Self::get_test_file(&TestEntry::get_test_file_path(input_file)),
                output: Self::get_test_file(&TestEntry::get_test_file_path(expected_file)),
                expected,
            }
        }

        fn get_test_file_path(filename: &str) -> String {
            let manifest_dir = env!("CARGO_MANIFEST_DIR");
            let tests_dir: PathBuf = [manifest_dir, "tests", filename].iter().collect();
            tests_dir.display().to_string()
        }

        fn get_test_file(path: &str) -> String {
            let content = fs::read_to_string(path).unwrap_or("".to_string());
            content.trim().to_string()
        }
    }

    #[test]
    fn test_notation_segment_parser() {
        let tests = vec![
            // Omitted date segment, everything else is defined.
            TestEntry::new(1, "1_notation.txt", "1_lothar.txt", Ok(())),
            // Omitted time segment, everything else is defined.
            //TestEntry {
            //    input: "12BFF·7·D·5 / [veth] / 9·2·A / C3 / A1 / B99D / [kal'mi]",
            //    expected: Ok(
            //        "tharyn'ath'bed'maren'eph'eph yen'ven kaemar'dol theren'saren /\nveth /\n",
            //    ),
            //},
        ];

        for test in tests {
            let mut p = NotationParser::new();
            let result = p.parse(&test.input);
            let i = test.id;

            match (&result, &test.expected) {
                (Ok(r1), Ok(_)) => {
                    let r2 = test.output;
                    assert_eq!(
                        **r1, r2,
                        "Test case {i} failed: result '{r1}' != expected '{r2}'"
                    )
                }
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
