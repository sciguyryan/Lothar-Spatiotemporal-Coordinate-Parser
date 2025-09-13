//! # Spatiotemporal Parser (Lôthar Sothar schema)
//!
//! This crate parses and validates the full *spatiotemporal coordinate*
//! format. **All seven segments must be present** (slash-separated), but any
//! segment may be **veiled** `[selm]` or **omitted** `[veth]` at the segment level:
//!
//! 1. **Date**: `cycle·year·month·day`
//! 2. **Time**: `hour·minute·second·tick` (may include inline `⟁` at the end)
//! 3. **Location**: one or more axes (hex) with an optional recursion decorator on the **whole** segment
//! 4. **Tier**: one or more two-hex codes (`00..FF`)
//! 5. **Folds**: uppercase 3-letter tags from an allowlist; each may carry a recursion decorator
//! 6. **Branch**: hex code (any length ≥ 1)
//! 7. **Modal Truth**: canonical token + required suffix `'mi` or `'da`
//!
//! Additional rules:
//! - **EBS** (`{X}`, `{X±N}`, `{A...B}`) is **only** allowed in **Date/Time/Location elements**, not in Tier/Folds/Branch/Modal.
//! - **Time-loop** `⟁` is allowed **only inline at the end of the Time segment** (e.g., `H·M·S·T⟁` or `H·M·S·T ⟁`). It is **not** a standalone slash segment.
//! - **Location recursion decorators** permitted on the **location segment only**: `~`, `~∞`, `~∂`, `~⊥`.
//! - **Fold tags** must be **uppercase** and in the allowlist; per-tag recursion decorators are allowed.
//! - **Whitespace** around separators (`/`, `·`) is ignored.
//!
//! ## Numeric bounds
//! - `cycle`: 1+ hex digits (no upper bound enforced by parser)
//! - `year`:  `0..FF` (1–2 hex digits)
//! - `month`: `0..F`  (1 hex)
//! - `day`:   `0..F`  (1 hex)
//! - `hour`:  `0..F`  (1 hex)
//! - `minute`: `0..3F` (1–2 hex)
//! - `second`: `0..3F` (1–2 hex)
//! - `tick`:   `0..FFFFFFFF` (1–8 hex)
//! - **Axes**: 1+ hex digits per axis; any number of axes
//! - **Tier**: chain of **exactly-two-hex** codes
//! - **Branch**: 1+ hex digits
//! - **Modal**: token in allowlist + `'mi`/`'da`
//!
//! ## Output
//! Returns a strongly typed [`Coordinate`] AST. Errors are categorized in [`ErrorKind`]
//! with helpful context. A canonical pretty-printer is provided via `Display`.
//!
//! ## Example
//! ```rust
//! use spatiotemporal_parser::parse;
//! use spatiotemporal_parser::Segment;
//! let input = "12BFF·7·D·A / 3·1F·2A·FF⟁ / 3·9·1C·1A~∞ / D2·A1 / ANN~⊥·DRM / B7C5 / kal'mi";
//! let coord = parse(input).expect("valid coordinate");
//! // Tier is a Segment<TierSegment>, not an Option, so match it:
//! match &coord.tier {
//!     Segment::Present(t) => assert_eq!(t.tiers.len(), 2),
//!     Segment::Veiled | Segment::Omitted => panic!("tier not present"),
//! }
//! ```

use core::fmt;

/// Allowlist of fold tags.
const ALLOWED_FOLD_TAGS: &[&str] = &[
    "ANN", "ARK", "CNS", "CYS", "DRM", "FAE", "INV", "NRV", "PEN", "PRX", "REC", "RLK", "SPR",
    "SYM", "TMP", "TRM",
];

// Allowlist for dream-fold tags.
const ALLOWED_DREAM_FOLD_TAGS: &[&str] = &[
    "CRY", "DSC", "FLX", "HLL", "INC", "LUC", "MNM", "NMR", "OBV", "PAL", "PSI", "REMGEN", "RVR",
    "SHR", "SNR", "SYMDRM",
];

/// Allowlist of modal truth tokens.
const ALLOWED_MODAL_TOKENS: &[&str] = &[
    "kal",
    "ven",
    "dūl",
    "inther'kael",
    "sarn",
    "soth",
    "vesh",
    "thur",
];

/// Top-level parse entry point.
pub fn parse(input: &str) -> Result<Coordinate, Error> {
    Parser::new(input).parse()
}

/// Recursion decorators permitted on Location (whole segment) and on Fold tags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[derive(Default)]
pub enum Recursion {
    #[default]
    None,
    Tilde,        // ~
    TildeInf,     // ~∞
    TildePartial, // ~∂
    TildeBottom,  // ~⊥
}


impl fmt::Display for Recursion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Recursion::None => write!(f, ""),
            Recursion::Tilde => write!(f, "~"),
            Recursion::TildeInf => write!(f, "~∞"),
            Recursion::TildePartial => write!(f, "~∂"),
            Recursion::TildeBottom => write!(f, "~⊥"),
        }
    }
}

/// Error-Bound Segment forms for a single value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ebs<T> {
    Exact(T),
    PlusMinus { center: T, delta: T },
    Range { start: T, end: T },
}

/// A Date segment: cycle·year·month·day
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DateSegment {
    pub cycle: ValueOrEbs<HexNum>,
    pub year: ValueOrEbs<HexNum>,
    pub month: ValueOrEbs<HexNum>,
    pub day: ValueOrEbs<HexNum>,
}

/// A non-linear timeflow indicator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TimeFlowMod {
    Nonlinear,               // ⪤
    RecurringConvergence,    // ⪤↻
    ReversibleOscillating,   // ⪤⇌
    MultidirectionalBraided, // ⪤⊞
    CrossThreaded,           // ⪤⊗
    VeiledFlux,              // ⪤⊘
    EntropicSink,            // ⪤↡
}

/// A time-loop state indicator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TimeLoop {
    Simple,        // "⟁"
    Infinite,      // "⟁∞"
    UntilBoundary, // "⟁∂"
    Paradox,       // "⟁⊥"
    Count(u32),    // "⟁" + 1..8 hex digits, >= 1
}

/// A Time segment: hour·minute·second·tick
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimeSegment {
    pub hour: ValueOrEbs<HexNum>,
    pub minute: ValueOrEbs<HexNum>,
    pub second: ValueOrEbs<HexNum>,
    pub tick: ValueOrEbs<HexNum>,
    pub vtfm: Option<TimeFlowMod>,
    pub loop_spec: Option<TimeLoop>,
}

/// Location segment: N axes (1+ hex digits each), and optional recursion decorator on the whole segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocationSegment {
    pub axes: Vec<ValueOrEbs<HexNum>>, // 1+ entries
    pub recursion: Recursion,
}

/// Dimensional tier: one or more elements, each exactly 2 hex digits (00..FF).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TierSegment {
    pub tiers: Vec<u8>,
}

/// Fold tag + optional recursion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldTag {
    pub tag: String, // Uppercase 3 letters.
    pub recursion: Recursion,
}

/// Fold chain: 1+ fold tags (if present).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldsSegment {
    pub folds: Vec<FoldTag>,
}

/// Branch segment: hex (1+ digits).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BranchSegment {
    pub code: String, // Normalized uppercase.
}

/// Modal truth segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModalTruthSegment {
    pub token: String,
    pub suffix: String, // "'mi" | "'da"
    pub inverted: bool, // True if prefixed with "na'"
}

/// Segment-veiling / omission controls the presence of a whole segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Segment<T> {
    Present(T),
    Veiled,  // [selm]
    Omitted, // [veth]
}

pub type Date = Segment<DateSegment>;
pub type Time = Segment<TimeSegment>;
pub type Location = Segment<LocationSegment>;
pub type Tier = Segment<TierSegment>;
pub type Folds = Segment<FoldsSegment>;
pub type Branch = Segment<BranchSegment>;
pub type Modal = Segment<ModalTruthSegment>;

/// A fully parsed Coordinate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coordinate {
    pub date: Date,
    pub time: Time,
    pub location: Location,
    pub tier: Tier,
    pub folds: Folds,
    pub branch: Branch,
    pub modal: Modal,
}

/// Error type with granular categories.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    WrongSegmentCount,
    InvalidHex,
    OutOfRange(&'static str),
    InvalidLength(&'static str),
    EbsNotAllowedHere,
    UnbalancedBraces,
    InvalidEbsSyntax(&'static str),
    InvalidDecorator,
    InvalidFoldTag,
    LowercaseFoldTag,
    InvalidModalTruth,
    InvalidTimeLoopPlacement,
    InvalidStructure(&'static str),
    DreamFoldWithoutDrm,
    InvAtEnd,
    VtfmMisplaced,
    VtfmUnknownDecorator,
    VtfmMultiple,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::WrongSegmentCount => {
                write!(f, "wrong number of segments (expected exactly 7)")
            }
            ErrorKind::InvalidHex => write!(f, "invalid hexadecimal value"),
            ErrorKind::OutOfRange(label) => write!(f, "value out of range for {label}"),
            ErrorKind::InvalidLength(label) => write!(f, "invalid length for {label}"),
            ErrorKind::EbsNotAllowedHere => {
                write!(f, "EBS notation is not allowed in this segment")
            }
            ErrorKind::UnbalancedBraces => write!(f, "unbalanced braces in EBS notation"),
            ErrorKind::InvalidEbsSyntax(msg) => write!(f, "invalid EBS syntax: {msg}"),
            ErrorKind::InvalidDecorator => write!(f, "invalid decorator symbol or placement"),
            ErrorKind::InvalidFoldTag => write!(f, "invalid fold tag"),
            ErrorKind::LowercaseFoldTag => write!(f, "fold tags must be uppercase"),
            ErrorKind::InvalidModalTruth => write!(f, "invalid modal truth particle"),
            ErrorKind::InvalidTimeLoopPlacement => {
                write!(f, "invalid time-loop marker (⟁) placement")
            }
            ErrorKind::InvalidStructure(msg) => write!(f, "invalid structure: {msg}"),
            ErrorKind::DreamFoldWithoutDrm => write!(
                f,
                "dream-fold tag requires a prior DRM tag in the fold chain"
            ),
            ErrorKind::InvAtEnd => write!(f, "INV cannot be the last fold tag"),
            ErrorKind::VtfmMisplaced => write!(f, "invalid placement of vectorial time flow (⪤)"),
            ErrorKind::VtfmUnknownDecorator => {
                write!(f, "unknown vectorial time flow decorator after ⪤")
            }
            ErrorKind::VtfmMultiple => {
                write!(f, "multiple vectorial time flow modifiers are not allowed")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub kind: ErrorKind,
    pub context: String,
}

impl Error {
    fn new(kind: ErrorKind, context: impl Into<String>) -> Self {
        Self {
            kind,
            context: context.into(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.context.is_empty() {
            write!(f, "{}", self.kind)
        } else {
            write!(f, "{} ({})", self.kind, self.context)
        }
    }
}

/// Hex number wrapper holding the normalized uppercase string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HexNum {
    pub text: String,
}

impl HexNum {
    fn parse_uppercased(s: &str) -> Result<Self, Error> {
        if s.is_empty() {
            return Err(Error::new(ErrorKind::InvalidHex, "empty"));
        }

        let up = s.trim().to_ascii_uppercase();
        if !up.chars().all(is_hex_char) {
            return Err(Error::new(ErrorKind::InvalidHex, s));
        }

        Ok(HexNum { text: up })
    }

    fn to_u128(&self) -> u128 {
        u128::from_str_radix(&self.text, 16).unwrap()
    }
}
#[inline]
fn is_hex_char(c: char) -> bool {
    c.is_ascii_hexdigit()
}

/// A value that may be wrapped in an EBS form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueOrEbs<T> {
    Value(T),
    Ebs(Ebs<T>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SegmentMark {
    Veiled,
    Omitted,
}

struct Parser<'a> {
    src: &'a str,
}
impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Self { src }
    }

    fn parse(&self) -> Result<Coordinate, Error> {
        let raw_parts: Vec<&str> = self.src.split('/').map(|s| s.trim()).collect();
        if raw_parts.len() != 7 {
            return Err(Error::new(
                ErrorKind::WrongSegmentCount,
                format!("expected 7 segments, got {}", raw_parts.len()),
            ));
        }

        // Forbid ⟁ anywhere except the *time* segment; also forbid a standalone "⟁" segment.
        for (i, part) in raw_parts.iter().enumerate() {
            let st = part.trim();
            if i != 1 && st.contains('⟁') {
                return Err(Error::new(
                    ErrorKind::InvalidTimeLoopPlacement,
                    "⟁ is only allowed as a suffix of the time segment",
                ));
            }

            if i != 1 && st.contains('⪤') {
                return Err(Error::new(
                    ErrorKind::VtfmMisplaced,
                    "⪤ is only allowed in the time segment",
                ));
            }
        }

        // If the time segment is a placeholder, it must be *exactly* the token with no loop.
        let tseg = raw_parts[1].trim();
        if (tseg.contains("[selm]") || tseg.contains("[veth]")) && tseg.contains('⟁') {
            return Err(Error::new(
                ErrorKind::InvalidTimeLoopPlacement,
                "⟁ cannot be combined with [selm]/[veth] in the time segment",
            ));
        }

        if (tseg.contains("[selm]") || tseg.contains("[veth]")) && tseg.contains('⪤') {
            return Err(Error::new(
                ErrorKind::VtfmMisplaced,
                "⪤ cannot be combined with [selm]/[veth]",
            ));
        }

        // None of the segments can be empty; use [veth]/[selm] if intentionally absent.
        if raw_parts.iter().any(|p| p.is_empty()) {
            return Err(Error::new(
                ErrorKind::InvalidStructure("empty segment: use [veth] or [selm] explicitly"),
                self.src,
            ));
        }

        let date = self.parse_date_segment(raw_parts[0])?;
        let time = self.parse_time_segment(raw_parts[1])?;
        let location = self.parse_location_segment(raw_parts[2])?;
        let tier = self.parse_tier_segment(raw_parts[3])?;
        let folds = self.parse_folds_segment(raw_parts[4])?;
        let branch = self.parse_branch_segment(raw_parts[5])?;
        let modal = self.parse_modal_segment(raw_parts[6])?;

        Ok(Coordinate {
            date,
            time,
            location,
            tier,
            folds,
            branch,
            modal,
        })
    }

    fn segment_mark(&self, s: &str) -> Option<SegmentMark> {
        match s.trim() {
            "[selm]" => Some(SegmentMark::Veiled),
            "[veth]" => Some(SegmentMark::Omitted),
            _ => None,
        }
    }

    fn split_dot(&self, s: &str) -> Vec<String> {
        // DO NOT filter out empties; callers must validate them.
        s.split('·').map(|t| t.trim().to_string()).collect()
    }

    fn parse_recursion_suffix(&self, s: &str) -> Result<(Recursion, String), Error> {
        // Allow whitespace before/after the decorator and between '~' and its symbol.
        let trimmed = s.trim_end();

        // Look for the last '~' (decorator applies to the entire location segment).
        if let Some(pos) = trimmed.rfind('~') {
            // Everything after '~' may have spaces and then one of: ∞, ∂, ⊥, or nothing.
            let tail = trimmed[pos + 1..].trim(); // e.g. "", "∞", "∂", "⊥"
            let rec = match tail {
                "" => Recursion::Tilde,
                "∞" => Recursion::TildeInf,
                "∂" => Recursion::TildePartial,
                "⊥" => Recursion::TildeBottom,
                _ => return Err(Error::new(ErrorKind::InvalidDecorator, &trimmed[pos..])),
            };
            // Core (axes) are everything before the '~', trimming trailing spaces.
            let core = trimmed[..pos].trim_end();
            return Ok((rec, core.to_string()));
        }

        Ok((Recursion::None, trimmed.to_string()))
    }

    fn parse_hex(&self, s: &str) -> Result<HexNum, Error> {
        HexNum::parse_uppercased(s)
    }

    fn parse_hex_with_len(
        &self,
        s: &str,
        min: usize,
        max: usize,
        label: &'static str,
    ) -> Result<HexNum, Error> {
        let h = self.parse_hex(s)?;
        let len = h.text.len();
        if len < min || len > max {
            return Err(Error::new(ErrorKind::InvalidLength(label), s));
        }

        Ok(h)
    }

    fn parse_value_or_ebs_hex(&self, s: &str) -> Result<ValueOrEbs<HexNum>, Error> {
        let st = s.trim();

        // If either brace is present, enforce that EBS wraps the WHOLE token: ^\{ .* \}$.
        let has_l = st.contains('{');
        let has_r = st.contains('}');
        if has_l ^ has_r {
            return Err(Error::new(ErrorKind::UnbalancedBraces, st));
        }

        if has_l || has_r {
            // Must be a single, outermost pair.
            if !(st.starts_with('{') && st.ends_with('}')) {
                return Err(Error::new(
                    ErrorKind::InvalidEbsSyntax("EBS must enclose the entire token"),
                    st,
                ));
            }

            let inner = &st[1..st.len() - 1].trim();
            if inner.is_empty() {
                return Err(Error::new(
                    ErrorKind::InvalidEbsSyntax("empty EBS body"),
                    st,
                ));
            }

            // Forbid nested braces anywhere inside the EBS body.
            if inner.contains('{') || inner.contains('}') {
                return Err(Error::new(
                    ErrorKind::InvalidEbsSyntax("nested EBS not allowed"),
                    st,
                ));
            }

            // Detect exactly one of: exact | ± | range.
            if let Some((a, b)) = inner.split_once('±') {
                let a = a.trim();
                let b = b.trim();
                if a.is_empty() || b.is_empty() {
                    return Err(Error::new(
                        ErrorKind::InvalidEbsSyntax("missing center or delta in ± form"),
                        st,
                    ));
                }

                return Ok(ValueOrEbs::Ebs(Ebs::PlusMinus {
                    center: self.parse_hex(a)?,
                    delta: self.parse_hex(b)?,
                }));
            }

            if let Some((a, b)) = inner.split_once("...") {
                let a = a.trim();
                let b = b.trim();
                if a.is_empty() || b.is_empty() {
                    return Err(Error::new(
                        ErrorKind::InvalidEbsSyntax("missing start or end in ... form"),
                        st,
                    ));
                }

                let start = self.parse_hex(a)?;
                let end = self.parse_hex(b)?;
                if start.to_u128() > end.to_u128() {
                    return Err(Error::new(
                        ErrorKind::InvalidEbsSyntax("range start > end"),
                        st,
                    ));
                }

                return Ok(ValueOrEbs::Ebs(Ebs::Range { start, end }));
            }

            // Otherwise treat as {X}.
            return Ok(ValueOrEbs::Ebs(Ebs::Exact(self.parse_hex(inner)?)));
        }

        // No braces → plain hex value.
        Ok(ValueOrEbs::Value(self.parse_hex(st)?))
    }

    fn validate_upper_cap(
        &self,
        v: &ValueOrEbs<HexNum>,
        cap: u128,
        label: &'static str,
    ) -> Result<(), Error> {
        let too_big = |x: u128| {
            if x > cap {
                Err(Error::new(ErrorKind::OutOfRange(label), format!("{x:X}")))
            } else {
                Ok(())
            }
        };

        match v {
            ValueOrEbs::Value(h) | ValueOrEbs::Ebs(Ebs::Exact(h)) => too_big(h.to_u128()),
            ValueOrEbs::Ebs(Ebs::PlusMinus { center, delta }) => {
                too_big(center.to_u128().saturating_add(delta.to_u128()))
            }
            ValueOrEbs::Ebs(Ebs::Range { start, end }) => {
                if start.to_u128() > end.to_u128() {
                    return Err(Error::new(
                        ErrorKind::InvalidEbsSyntax("range start > end"),
                        "",
                    )); // If not already checked.
                }

                too_big(end.to_u128())
            }
        }
    }

    fn assert_no_ebs_here(&self, raw: &str) -> Result<(), Error> {
        // Quick syntactic guard - any brace-wrapped token is considered EBS.
        let has = raw.contains('{') || raw.contains('}');
        if has {
            Err(Error::new(ErrorKind::EbsNotAllowedHere, raw))
        } else {
            Ok(())
        }
    }

    fn parse_date_segment(&self, s: &str) -> Result<Date, Error> {
        if let Some(mark) = self.segment_mark(s) {
            return Ok(match mark {
                SegmentMark::Veiled => Segment::Veiled,
                SegmentMark::Omitted => Segment::Omitted,
            });
        }
        let parts = self.split_dot(s);
        if parts.len() != 4 {
            return Err(Error::new(
                ErrorKind::InvalidStructure("date requires 4 parts: cycle·year·month·day"),
                s,
            ));
        }
        let cycle = self.parse_value_or_ebs_hex(&parts[0])?;
        let year = self.parse_value_or_ebs_hex(&parts[1])?;
        let month = self.parse_value_or_ebs_hex(&parts[2])?;
        let day = self.parse_value_or_ebs_hex(&parts[3])?;

        self.validate_upper_cap(&year, 0xFF, "year")?;
        self.validate_upper_cap(&month, 0xF, "month")?;
        self.validate_upper_cap(&day, 0xF, "day")?;

        Ok(Segment::Present(DateSegment {
            cycle,
            year,
            month,
            day,
        }))
    }

    fn parse_time_segment(&self, s: &str) -> Result<Segment<TimeSegment>, Error> {
        if let Some(mark) = self.segment_mark(s) {
            return Ok(match mark {
                SegmentMark::Veiled => Segment::Veiled,
                SegmentMark::Omitted => Segment::Omitted,
            });
        }

        // First, extract loop (suffix at very end).
        let st = s.trim();
        let (mut st, loop_spec) = self.extract_time_loop_suffix(st)?;

        // Ensure no stray loop particle is left, if we found one.
        if loop_spec.is_some() && st.contains('⟁') {
            return Err(Error::new(
                ErrorKind::InvalidTimeLoopPlacement,
                "multiple or misplaced ⟁ markers",
            ));
        }

        // If we found a loop, the body before it must be a valid time.
        if loop_spec.is_some() {
            self.preflight_time_before_loop(st)?;
        }

        // Next, extract optional VTFM - just after tick, i.e., now at the end.
        let (st2, vtfm) = self.extract_vtfm_suffix(st)?;
        st = st2;

        // Ensure no stray VTFM particle is left.
        if st.contains('⪤') {
            return Err(Error::new(
                ErrorKind::VtfmMisplaced,
                "⪤ must appear once at end of time (but before any ⟁)",
            ));
        }

        // Finally, parse fields and enforce caps.
        let (hour, minute, second, tick) = self.parse_time_fields(st)?;
        self.validate_upper_cap(&hour, 0xF, "hour")?;
        self.validate_upper_cap(&minute, 0x3F, "minute")?;
        self.validate_upper_cap(&second, 0x3F, "second")?;
        self.validate_upper_cap(&tick, 0xFFFF_FFFF, "tick")?;

        Ok(Segment::Present(TimeSegment {
            hour,
            minute,
            second,
            tick,
            vtfm,
            loop_spec,
        }))
    }

    /// Strip a trailing time-loop suffix (`⟁`, `⟁∞`, `⟁∂`, `⟁⊥`, or `⟁` + 1–8 hex).
    /// Returns (remainder_without_loop, Some(loop)) or (input, None).
    fn extract_time_loop_suffix<'b>(
        &self,
        s: &'a str,
    ) -> Result<(&'a str, Option<TimeLoop>), Error> {
        let st = s.trim_end();

        if let Some(prefix) = st.strip_suffix("⟁∞") {
            return Ok((prefix.trim_end(), Some(TimeLoop::Infinite)));
        }
        if let Some(prefix) = st.strip_suffix("⟁∂") {
            return Ok((prefix.trim_end(), Some(TimeLoop::UntilBoundary)));
        }
        if let Some(prefix) = st.strip_suffix("⟁⊥") {
            return Ok((prefix.trim_end(), Some(TimeLoop::Paradox)));
        }
        if let Some(prefix) = st.strip_suffix('⟁') {
            return Ok((prefix.trim_end(), Some(TimeLoop::Simple)));
        }

        if let Some(pos) = st.rfind('⟁') {
            let tail = st[pos + '⟁'.len_utf8()..].trim();
            if !tail.is_empty() && tail.len() <= 8 && tail.chars().all(|c| c.is_ascii_hexdigit()) {
                let up = tail.to_ascii_uppercase();
                let n = u32::from_str_radix(&up, 16).map_err(|_| {
                    Error::new(ErrorKind::InvalidTimeLoopPlacement, "invalid loop count")
                })?;
                if n == 0 {
                    return Err(Error::new(
                        ErrorKind::InvalidTimeLoopPlacement,
                        "time-loop count must be >= 1",
                    ));
                }
                let head = st[..pos].trim_end();
                return Ok((head, Some(TimeLoop::Count(n))));
            } else {
                return Err(Error::new(
                    ErrorKind::InvalidTimeLoopPlacement,
                    "⟁ must appear once at end (optionally with ∞/∂/⊥ or 1..8 hex)",
                ));
            }
        }

        Ok((st, None))
    }

    /// Remove a single trailing VTFM marker from the end of `s` and return the prefix.
    /// Accepts bare `⪤` or decorated `⪤↻/⇌/⊞/⊗/⊘/↡`. Returns (remainder, vtfm_option).
    fn extract_vtfm_suffix<'b>(&self, s: &'b str) -> Result<(&'b str, Option<TimeFlowMod>), Error> {
        let mut st = s.trim_end();
        let vtfm: Option<TimeFlowMod>;

        macro_rules! try_vtfm {
            ($pat:literal, $variant:expr) => {
                if let Some(prefix) = st.strip_suffix($pat) {
                    vtfm = Some($variant);
                    st = prefix.trim_end();
                    return Ok((st, vtfm));
                }
            };
        }

        // Decorated VTFM particles first.
        try_vtfm!("⪤↻", TimeFlowMod::RecurringConvergence);
        try_vtfm!("⪤⇌", TimeFlowMod::ReversibleOscillating);
        try_vtfm!("⪤⊞", TimeFlowMod::MultidirectionalBraided);
        try_vtfm!("⪤⊗", TimeFlowMod::CrossThreaded);
        try_vtfm!("⪤⊘", TimeFlowMod::VeiledFlux);
        try_vtfm!("⪤↡", TimeFlowMod::EntropicSink);

        // And a bare VTFM particle if those fail.
        if st.ends_with('⪤') {
            let cut = &st[..st.len() - '⪤'.len_utf8()];
            return Ok((cut.trim_end(), Some(TimeFlowMod::Nonlinear)));
        }

        // If some ⪤ exists but not in a recognised suffix position.
        if let Some(pos) = st.rfind('⪤') {
            let tail = st[pos + '⪤'.len_utf8()..].trim_end();
            if !tail.is_empty()
                && tail != "↻"
                && tail != "⇌"
                && tail != "⊞"
                && tail != "⊗"
                && tail != "⊘"
                && tail != "↡"
            {
                return Err(Error::new(ErrorKind::VtfmUnknownDecorator, tail));
            }
        }

        Ok((st, None))
    }

    /// When a loop is present, ensure what precedes it is a *valid time shape* (with optional VTFM),
    /// and that the tick token (post optional VTFM) looks hex-ish if not an EBS.
    fn preflight_time_before_loop(&self, st: &str) -> Result<(), Error> {
        let preview = self.split_dot(st);
        if preview.len() != 4 {
            return Err(Error::new(
                ErrorKind::InvalidTimeLoopPlacement,
                "loop must directly follow a valid time (hour·minute·second·tick [⪤…])",
            ));
        }

        let mut tick_preview = preview[3].trim_end();

        // Strip one trailing VTFM if present.
        for pat in ["⪤↻", "⪤⇌", "⪤⊞", "⪤⊗", "⪤⊘", "⪤↡"] {
            if tick_preview.ends_with(pat) {
                tick_preview = tick_preview[..tick_preview.len() - pat.len()].trim_end();
                break;
            }
        }
        if tick_preview.ends_with('⪤') {
            tick_preview = tick_preview[..tick_preview.len() - '⪤'.len_utf8()].trim_end();
        }

        // If not an EBS token, it must look like ≤8 hex.
        if !tick_preview.contains('{') && !tick_preview.contains('}')
            && (tick_preview.is_empty()
                || tick_preview.len() > 8
                || !tick_preview.chars().all(|c| c.is_ascii_hexdigit()))
            {
                return Err(Error::new(
                    ErrorKind::InvalidTimeLoopPlacement,
                    "loop must directly follow a valid tick (≤8 hex)",
                ));
            }
        Ok(())
    }

    /// Parse the 4 dot-separated time fields into ValueOrEbs<HexNum>, without caps.
    fn parse_time_fields(
        &self,
        st: &str,
    ) -> Result<
        (
            ValueOrEbs<HexNum>,
            ValueOrEbs<HexNum>,
            ValueOrEbs<HexNum>,
            ValueOrEbs<HexNum>,
        ),
        Error,
    > {
        let parts = self.split_dot(st);
        if parts.len() != 4 {
            return Err(Error::new(
                ErrorKind::InvalidStructure("time requires hour·minute·second·tick"),
                st,
            ));
        }

        let hour = self.parse_value_or_ebs_hex(&parts[0])?;
        let minute = self.parse_value_or_ebs_hex(&parts[1])?;
        let second = self.parse_value_or_ebs_hex(&parts[2])?;
        let tick = self.parse_value_or_ebs_hex(&parts[3])?;

        Ok((hour, minute, second, tick))
    }

    fn parse_location_segment(&self, s: &str) -> Result<Location, Error> {
        if let Some(mark) = self.segment_mark(s) {
            return Ok(match mark {
                SegmentMark::Veiled => Segment::Veiled,
                SegmentMark::Omitted => Segment::Omitted,
            });
        }

        let (rec, core) = self.parse_recursion_suffix(s.trim())?;
        let parts = self.split_dot(&core);
        if parts.is_empty() {
            return Err(Error::new(
                ErrorKind::InvalidStructure("location requires at least 1 axis"),
                s,
            ));
        }

        let mut axes = Vec::with_capacity(parts.len());
        for p in parts {
            axes.push(self.parse_value_or_ebs_hex(&p)?);
        }

        Ok(Segment::Present(LocationSegment {
            axes,
            recursion: rec,
        }))
    }

    fn parse_tier_segment(&self, s: &str) -> Result<Tier, Error> {
        if let Some(mark) = self.segment_mark(s) {
            return Ok(match mark {
                SegmentMark::Veiled => Segment::Veiled,
                SegmentMark::Omitted => Segment::Omitted,
            });
        }

        self.assert_no_ebs_here(s)?;
        let parts = self.split_dot(s);
        if parts.is_empty() {
            return Err(Error::new(
                ErrorKind::InvalidStructure("tier cannot be empty"),
                s,
            ));
        }

        let mut tiers = Vec::with_capacity(parts.len());
        for p in parts {
            if p.is_empty() {
                return Err(Error::new(ErrorKind::InvalidLength("tier(2-hex)"), s));
            }

            let h = self.parse_hex_with_len(&p, 2, 2, "tier(2-hex)")?;
            let v = u8::from_str_radix(&h.text, 16)
                .map_err(|_| Error::new(ErrorKind::InvalidHex, p))?;
            tiers.push(v);
        }

        Ok(Segment::Present(TierSegment { tiers }))
    }

    fn parse_folds_segment(&self, s: &str) -> Result<Folds, Error> {
        if let Some(mark) = self.segment_mark(s) {
            return Ok(match mark {
                SegmentMark::Veiled => Segment::Veiled,
                SegmentMark::Omitted => Segment::Omitted,
            });
        }

        self.assert_no_ebs_here(s)?;

        let parts = self.split_dot(s);
        if parts.is_empty() {
            return Err(Error::new(
                ErrorKind::InvalidStructure("folds cannot be empty"),
                s,
            ));
        }

        let mut folds: Vec<FoldTag> = Vec::with_capacity(parts.len());
        let mut has_seen_drm = false;

        for raw in parts {
            if raw.is_empty() {
                return Err(Error::new(ErrorKind::InvalidFoldTag, s));
            }

            let (recursion, core) = self.parse_recursion_suffix(&raw)?;
            let tag = core.trim();

            // The value may be a numeric fold code (00..FF), case-insensitive.
            if tag.len() == 2 && tag.chars().all(|c| c.is_ascii_hexdigit()) {
                let code = tag.to_ascii_uppercase();
                folds.push(FoldTag {
                    tag: code,
                    recursion,
                }); // Store canonically.
                continue;
            }

            // Tags should only ever be in upper case (symbolic tags).
            if tag.is_empty() || !tag.chars().all(|c| c.is_ascii_uppercase()) {
                if tag.chars().any(|c| c.is_ascii_lowercase()) {
                    return Err(Error::new(ErrorKind::LowercaseFoldTag, tag));
                }
                return Err(Error::new(ErrorKind::InvalidFoldTag, tag));
            }

            let is_normal = ALLOWED_FOLD_TAGS.contains(&tag);
            let is_dream = ALLOWED_DREAM_FOLD_TAGS.contains(&tag);

            // Must be either a normal fold or a dream-fold.
            if !(is_normal || is_dream) {
                return Err(Error::new(ErrorKind::InvalidFoldTag, tag));
            }

            // Dream-folds allowed only if a prior tag in the chain is DRM.
            if is_dream && !has_seen_drm {
                return Err(Error::new(ErrorKind::DreamFoldWithoutDrm, tag));
            }

            // Record DRM occurrence in the chain.
            if tag == "DRM" {
                has_seen_drm = true;
            }

            folds.push(FoldTag {
                tag: tag.to_string(),
                recursion,
            });
        }

        // INV may never be last.
        if let Some(last) = folds.last()
            && last.tag == "INV" {
                return Err(Error::new(ErrorKind::InvAtEnd, &last.tag));
            }

        Ok(Segment::Present(FoldsSegment { folds }))
    }

    fn parse_branch_segment(&self, s: &str) -> Result<Branch, Error> {
        if let Some(mark) = self.segment_mark(s) {
            return Ok(match mark {
                SegmentMark::Veiled => Segment::Veiled,
                SegmentMark::Omitted => Segment::Omitted,
            });
        }

        // EBS is forbidden in timeline branch.
        self.assert_no_ebs_here(s)?;

        let h = self.parse_hex(s.trim())?;
        Ok(Segment::Present(BranchSegment { code: h.text }))
    }

    fn parse_modal_segment(&self, s: &str) -> Result<Modal, Error> {
        // Canonicalise curly apostrophes to ASCII "'".
        let st = s.trim().replace('\u{2019}', "'");

        // Modal segment may be veiled but NOT omitted.
        if let Some(mark) = self.segment_mark(&st) {
            return match mark {
                SegmentMark::Veiled => Ok(Segment::Veiled),
                SegmentMark::Omitted => Err(Error::new(
                    ErrorKind::InvalidStructure("modal cannot be omitted"),
                    s,
                )),
            };
        }

        // Brackets are reserved for placeholders; any remaining '[' or ']' is invalid here.
        if st.contains('[') || st.contains(']') {
            return Err(Error::new(
                ErrorKind::InvalidStructure("brackets are reserved for placeholders"),
                s,
            ));
        }

        // EBS is forbidden in modal.
        self.assert_no_ebs_here(&st)?;

        // Split into (core, optional suffix "'mi" / "'da").
        let (core_maybe_na, suffix): (&str, &'static str) =
            if let Some(core) = st.strip_suffix("'mi") {
                (core.trim_end(), "'mi")
            } else if let Some(core) = st.strip_suffix("'da") {
                (core.trim_end(), "'da")
            } else {
                // No suffix — accept bare divine particle
                (st.as_str(), "")
            };

        // Optional inversion prefix `na'` ONLY at the beginning, no spaces, only once.
        let (inverted, token_str) = if let Some(rest) = core_maybe_na.strip_prefix("na'") {
            if rest.starts_with(char::is_whitespace) || rest.contains("na'") || rest.is_empty() {
                return Err(Error::new(
                    ErrorKind::InvalidModalTruth,
                    "na' may appear once, only as a prefix, with no space",
                ));
            }
            (true, rest)
        } else {
            (false, core_maybe_na)
        };

        // Disallow any whitespace inside the modal token.
        if token_str.is_empty() || token_str.contains(char::is_whitespace) {
            return Err(Error::new(
                ErrorKind::InvalidModalTruth,
                "invalid spacing in modal token",
            ));
        }

        // Validate base token against the allowlist.
        if !ALLOWED_MODAL_TOKENS.contains(&token_str) {
            return Err(Error::new(ErrorKind::InvalidModalTruth, token_str));
        }

        Ok(Segment::Present(ModalTruthSegment {
            token: token_str.to_string(),
            suffix: suffix.to_string(), // "" for bare; "'mi" or "'da" for suffixed.
            inverted,
        }))
    }
}

impl fmt::Display for Coordinate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} / ", display_segment(&self.date, display_date))?;
        write!(f, "{}", display_segment(&self.time, display_time))?;
        write!(f, " / ")?;
        write!(f, "{}", display_segment(&self.location, display_location))?;
        write!(f, " / {}", display_segment(&self.tier, display_tier))?;
        write!(f, " / {}", display_segment(&self.folds, display_folds))?;
        write!(f, " / {}", display_segment(&self.branch, display_branch))?;
        write!(f, " / {}", display_segment(&self.modal, display_modal))?;
        Ok(())
    }
}

fn display_segment<T>(s: &Segment<T>, inner: fn(&T) -> String) -> String {
    match s {
        Segment::Present(v) => inner(v),
        Segment::Veiled => "[selm]".to_string(),
        Segment::Omitted => "[veth]".to_string(),
    }
}

fn display_date(d: &DateSegment) -> String {
    format!(
        "{}·{}·{}·{}",
        display_val_compact(&d.cycle),
        display_val_compact(&d.year),
        display_val_compact(&d.month),
        display_val_compact(&d.day)
    )
}

fn display_time(t: &TimeSegment) -> String {
    let mut out = format!(
        "{}·{}·{}·{}",
        display_val_compact(&t.hour),
        display_val_compact(&t.minute),
        display_val_compact(&t.second),
        display_val_compact(&t.tick)
    );

    // Vectorial Time Flow Modifiers (VTFM), if present, come directly after
    // the ticks.
    if let Some(m) = &t.vtfm {
        match m {
            TimeFlowMod::RecurringConvergence => out.push_str("⪤↻"),
            TimeFlowMod::ReversibleOscillating => out.push_str("⪤⇌"),
            TimeFlowMod::MultidirectionalBraided => out.push_str("⪤⊞"),
            TimeFlowMod::CrossThreaded => out.push_str("⪤⊗"),
            TimeFlowMod::VeiledFlux => out.push_str("⪤⊘"),
            TimeFlowMod::EntropicSink => out.push_str("⪤↡"),
            TimeFlowMod::Nonlinear => out.push('⪤'),
        }
    }

    // Time loop modifiers, if present, come directly after the
    // VTFMs.
    if let Some(l) = &t.loop_spec {
        match l {
            TimeLoop::Simple => out.push('⟁'),
            TimeLoop::Infinite => out.push_str("⟁∞"),
            TimeLoop::UntilBoundary => out.push_str("⟁∂"),
            TimeLoop::Paradox => out.push_str("⟁⊥"),
            TimeLoop::Count(n) => {
                out.push_str(&format!("⟁{n:X}"));
            }
        }
    }

    out
}

fn display_location(l: &LocationSegment) -> String {
    let axes = l
        .axes
        .iter()
        .map(display_val_compact)
        .collect::<Vec<_>>()
        .join("·");
    format!("{axes}{}", l.recursion)
}

fn display_tier(t: &TierSegment) -> String {
    t.tiers
        .iter()
        .map(|v| format!("{v:02X}"))
        .collect::<Vec<_>>()
        .join("·")
}

fn display_folds(s: &FoldsSegment) -> String {
    s.folds
        .iter()
        .map(|f| format!("{}{}", f.tag, f.recursion))
        .collect::<Vec<_>>()
        .join("·")
}

fn display_branch(b: &BranchSegment) -> String {
    b.code.clone()
}

fn display_modal(m: &ModalTruthSegment) -> String {
    if m.inverted {
        format!("na'{}{}", m.token, m.suffix)
    } else {
        format!("{}{}", m.token, m.suffix)
    }
}

fn display_val_compact(v: &ValueOrEbs<HexNum>) -> String {
    match v {
        ValueOrEbs::Value(h) => compact_hex_str(&h.text),
        ValueOrEbs::Ebs(Ebs::Exact(h)) => format!("{{{}}}", compact_hex_str(&h.text)),
        ValueOrEbs::Ebs(Ebs::PlusMinus { center, delta }) => format!(
            "{{{}±{}}}",
            compact_hex_str(&center.text),
            compact_hex_str(&delta.text)
        ),
        ValueOrEbs::Ebs(Ebs::Range { start, end }) => format!(
            "{{{}...{}}}",
            compact_hex_str(&start.text),
            compact_hex_str(&end.text)
        ),
    }
}

fn compact_hex_str(s: &str) -> String {
    let t = s.trim_start_matches('0');
    if t.is_empty() {
        "0".to_string()
    } else {
        t.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    fn ok(input: &str) -> Coordinate {
        parse(input).expect("should parse")
    }

    fn err(input: &str) -> ErrorKind {
        match parse(input) {
            Ok(_) => panic!("expected error"),
            Err(e) => e.kind,
        }
    }

    fn loc_axes(c: &Coordinate) -> &[ValueOrEbs<HexNum>] {
        match &c.location {
            Segment::Present(l) => &l.axes,
            _ => panic!("location not present"),
        }
    }

    fn folds_vec(c: &Coordinate) -> &[FoldTag] {
        match &c.folds {
            Segment::Present(f) => &f.folds,
            _ => panic!("folds not present"),
        }
    }

    fn branch_code(c: &Coordinate) -> &str {
        match &c.branch {
            Segment::Present(b) => &b.code,
            _ => panic!("branch not present"),
        }
    }

    #[test]
    fn requires_exactly_7_segments() {
        let k = err("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7"); // 6
        assert!(matches!(k, ErrorKind::WrongSegmentCount));

        let k = err("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7 / kal'mi / extra"); // 8
        assert!(matches!(k, ErrorKind::WrongSegmentCount));
    }

    #[test]
    fn empty_segment_is_invalid_use_veth_or_selm() {
        let k = err("A·0·0·0 / 0·0·0·0 /  / 00 / ANN / B7 / kal'mi");
        assert!(matches!(k, ErrorKind::InvalidStructure(_)));
    }

    #[test]
    fn placeholders_keep_structure() {
        let _ = ok("[selm] / [veth] / [selm] / [veth] / ANN / 0 / kal'mi");
        assert!(matches!(
            err("[selm] / [veth] / [selm] /  / ANN / 0 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    #[test]
    fn placeholders_must_be_exact_token_in_all_segments() {
        assert!(matches!(
            err("[selm] ~⊥ / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));

        assert!(matches!(
            err("[veth]foo / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    #[test]
    fn parses_full_example_with_inline_loop_and_decorators() {
        let s = "12BFF·7·D·A / 3·1F·2A·FF⟁ / 3·9·1C·1A~∞ / D2·A1 / ANN~⊥·DRM / B7C5 / kal'mi";
        let c = ok(s);

        match &c.time {
            Segment::Present(t) => assert!(matches!(t.loop_spec, Some(TimeLoop::Simple))),
            _ => panic!("time segment not present"),
        }

        assert!(matches!(c.tier, Segment::Present(_)));
        assert!(matches!(c.folds, Segment::Present(_)));
        assert!(matches!(c.branch, Segment::Present(_)));
        assert!(matches!(c.modal, Segment::Present(_)));
    }

    #[test]
    fn loop_cannot_be_a_separate_segment() {
        let k = err("A·0·0·0 / 0·0·0·0 / F / ⟁ / 00 / ANN / kal'mi");
        assert!(matches!(k, ErrorKind::InvalidTimeLoopPlacement));
    }

    #[test]
    fn loop_marker_misplacement() {
        // Date
        assert!(matches!(
            err("0·0·0·0⟁ / 0·0·0·0 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
        // Location
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 1·2·3⟁ / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
        // Tier
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 0A·FF⟁ / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
        // Folds
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN⟁ / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
        // Branch
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / BEEF⟁ / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
        // Modal
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi⟁"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
    }

    #[test]
    fn time_loop_accepts_count_and_symbols_only_at_end() {
        ok("0·0·0·0 / 0·0·0·0⟁ / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁A / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁∞ / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁∂ / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁⊥ / 0 / 00 / ANN / 0 / kal");

        // Not at end / multiple / junk before marker.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁⟁ / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0foo⟁A / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
    }

    #[test]
    fn time_placeholder_with_loop_marker_is_rejected() {
        assert!(matches!(
            err("0·0·0·0 / [selm]⟁ / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        assert!(matches!(
            err("0·0·0·0 / [veth]⟁ / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
    }

    #[test]
    fn time_placeholder_exact_is_ok() {
        let _ = ok("0·0·0·0 / [selm] / 0 / 00 / ANN / 0 / kal'mi");
        let _ = ok("0·0·0·0 / [veth] / 0 / 00 / ANN / 0 / kal'mi");
    }

    #[test]
    fn time_placeholder_with_trailing_garbage_is_rejected() {
        assert!(matches!(
            err("0·0·0·0 / [selm] ~ ⊥ / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));

        assert!(matches!(
            err("0·0·0·0 / [veth]foo / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    #[test]
    fn tier_two_hex_parsing_and_validation() {
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 0a·ff·01 / ANN / 0 / kal'mi");
        if let Segment::Present(t) = c.tier {
            assert_eq!(t.tiers, vec![0x0A, 0xFF, 0x01]);
        } else {
            panic!();
        }

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / A / ANN / 1 / ven'da"),
            ErrorKind::InvalidLength("tier(2-hex)")
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 0AF / ANN / 1 / ven'da"),
            ErrorKind::InvalidLength("tier(2-hex)")
        ));
    }

    #[test]
    fn folds_uppercase_only_and_allowlisted() {
        let _ = ok("A·0·0·0 / 0·0·0·0 / F / 00 / ANN·DRM / B7 / kal'mi");
        let k = err("A·0·0·0 / 0·0·0·0 / F / 00 / ann / B7 / kal'mi");
        assert!(matches!(k, ErrorKind::LowercaseFoldTag));

        let k = err("A·0·0·0 / 0·0·0·0 / F / 00 / XYZ / B7 / kal'mi");
        assert!(matches!(k, ErrorKind::InvalidFoldTag));
    }

    #[test]
    fn folds_with_various_decorators() {
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN~·DRM~∞·NRV~∂·TMP~⊥ / 1 / soth'mi");
        assert_eq!(folds_vec(&c).len(), 4);
    }

    #[test]
    fn folds_and_tier_require_nonempty_items() {
        // Empty fold item.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN··DRM / 0 / kal'mi"),
            ErrorKind::InvalidFoldTag
        ));

        // Empty tier item.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 0A··FF / ANN / 0 / kal'mi"),
            ErrorKind::InvalidLength("tier(2-hex)")
        ));
    }

    #[test]
    fn ebs_not_allowed_in_folds() {
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·{DRM} / 0 / kal'mi"),
            ErrorKind::EbsNotAllowedHere
        ));
    }

    #[test]
    fn modal_suffix_and_token_checks() {
        // Valid particle with curly apostrophe canonicalised.
        let c = ok("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7 / dūl’mi");
        let m = match c.modal {
            Segment::Present(m) => m,
            _ => unreachable!(),
        };
        assert_eq!(m.token, "dūl");
        assert_eq!(m.suffix, "'mi");

        // Bare particle without suffix.
        // Valid, but may only be used by divine beings that
        // can declare an absolute truth.
        let c = ok("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7 / dūl");
        let m = match c.modal {
            Segment::Present(m) => m,
            _ => unreachable!(),
        };
        assert_eq!(m.token, "dūl");
        assert_eq!(m.suffix, "");

        // Bare particle without suffix, and with a "'na" inversion.
        // Valid, but may only be used by divine beings that
        // can declare an absolute truth.
        let c = ok("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7 / na'dūl");
        let m = match c.modal {
            Segment::Present(m) => m,
            _ => unreachable!(),
        };
        assert_eq!(m.inverted, true);
        assert_eq!(m.token, "dūl");
        assert_eq!(m.suffix, "");

        // Bate particle containing a "'".
        // Valid, but may only be used by divine beings that
        // can declare an absolute truth.
        let c = ok("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7 / inther'kael");
        let m = match c.modal {
            Segment::Present(m) => m,
            _ => unreachable!(),
        };
        assert_eq!(m.token, "inther'kael");
        assert_eq!(m.suffix, "");

        // Token not in allowlist.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / nope'da"),
            ErrorKind::InvalidModalTruth
        ));
    }

    #[test]
    fn modal_is_never_bracketed() {
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / [kal'mi]"),
            ErrorKind::InvalidStructure(_)
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / [na'soth'da]"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    #[test]
    fn modal_cannot_be_omitted_but_can_be_veiled() {
        let _ = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / [selm]");
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / [veth]"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    #[test]
    fn modal_inversion_accepts_na_prefix() {
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na'kal'mi");
        match c.modal {
            Segment::Present(m) => {
                assert_eq!(m.token, "kal");
                assert_eq!(m.suffix, "'mi");
                assert!(m.inverted);
            }
            _ => panic!("modal not present"),
        }

        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na'inther'kael'da");
        match c.modal {
            Segment::Present(m) => {
                assert_eq!(m.token, "inther'kael");
                assert_eq!(m.suffix, "'da");
                assert!(m.inverted);
            }
            _ => panic!("modal not present"),
        }
    }

    #[test]
    fn modal_inversion_misuse_is_rejected() {
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / kal'na'mi"),
            ErrorKind::InvalidModalTruth
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na' kal'mi"),
            ErrorKind::InvalidModalTruth
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na'na'kal'mi"),
            ErrorKind::InvalidModalTruth
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na'nope'mi"),
            ErrorKind::InvalidModalTruth
        ));
    }

    #[test]
    fn modal_inversion_round_trip_display() {
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na'soth'da");
        let out = format!("{c}");
        assert!(out.ends_with("na'soth'da"));
    }

    #[test]
    fn ebs_allowed_only_in_date_time_location() {
        let _ = ok("A·FF·{A±1}·{B...D} / 0·{3E±1}·2·1 / {10±2}·20·30 / 00 / ANN / B7 / kal'mi");
        assert!(matches!(
            err("A·FF·0·0 / 0·0·0·0 / F / {0A} / ANN / B7 / kal'mi"),
            ErrorKind::EbsNotAllowedHere
        ));

        assert!(matches!(
            err("A·FF·0·0 / 0·0·0·0 / F / 0A / ANN / {BEEF} / kal'mi"),
            ErrorKind::EbsNotAllowedHere
        ));

        assert!(matches!(
            err("A·FF·0·0 / 0·0·0·0 / F / 0A / ANN·{DRM} / B7 / kal'mi"),
            ErrorKind::EbsNotAllowedHere
        ));

        assert!(matches!(
            err("A·FF·0·0 / 0·0·0·0 / F / 0A / ANN / BEEF / {kal'mi}"),
            ErrorKind::EbsNotAllowedHere
        ));
    }

    #[test]
    fn ebss_unbalanced_and_malformed_are_clear_errors() {
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·{FF / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::UnbalancedBraces
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·FF} / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::UnbalancedBraces
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·A{FF} / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·{} / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·{±1}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·{3F±}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·{...3F}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·{3F...}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));
        ok("0·00·0·0 / 0·{3E±1}·{2...3}·{FF} / 0 / 00 / ANN / 0 / kal'mi");
    }

    #[test]
    fn ebs_range_requires_start_le_end_and_no_nesting() {
        assert!(matches!(
            err("0·0·0·0 / 0·{5...3}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·{{3}±1}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));
    }

    #[test]
    fn ebs_plusminus_upper_endpoint_checked_only() {
        ok("0·00·0·0 / {1}·0·0·0 / {1±5}·2·3·4 / 00 / ANN / 0 / kal'mi");
        let k = err("0·00·0·0 / 0·{2±3E}·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        assert!(matches!(k, ErrorKind::OutOfRange("minute")));
    }

    #[test]
    fn ebs_range_upper_bound_checked_only() {
        ok("0·00·0·0 / 0·{0...3F}·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        let k = err("0·00·0·0 / 0·{0...40}·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        assert!(matches!(k, ErrorKind::OutOfRange("minute")));
    }

    #[test]
    fn year_ebs_respects_cap_on_end_only() {
        ok("0·{0...FF}·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        let k = err("0·{0...1FF}·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        assert!(matches!(k, ErrorKind::OutOfRange("year")));
    }

    #[test]
    fn location_with_multiple_axes_and_decorator() {
        let c = ok("A·0·0·0 / 0·0·0·0 / 1·2·3·4~∂ / 00 / ANN / B7 / kal'mi");
        let loc = match c.location {
            Segment::Present(l) => l,
            _ => unreachable!(),
        };
        assert_eq!(loc.axes.len(), 4);
        assert_eq!(loc.recursion, Recursion::TildePartial);
    }

    #[test]
    fn location_decorator_whitespace_variants() {
        let c1 = ok("0·00·0·0 / 0·0·0·0 / 1·2·3~⊥ / 00 / ANN / 0 / kal'mi");
        let c2 = ok("0·00·0·0 / 0·0·0·0 / 1·2·3 ~⊥ / 00 / ANN / 0 / kal'mi");
        let c3 = ok("0·00·0·0 / 0·0·0·0 / 1·2·3~ ⊥ / 00 / ANN / 0 / kal'mi");
        assert_eq!(loc_axes(&c1).len(), 3);
        assert_eq!(loc_axes(&c2).len(), 3);
        assert_eq!(loc_axes(&c3).len(), 3);
    }

    #[test]
    fn invalid_location_decorator_symbol() {
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 1·2·3~? / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidDecorator
        ));
    }

    #[test]
    fn location_rejects_empty_axis_item() {
        let k = err("0·0·0·0 / 0·0·0·0 / 1··2 / 00 / ANN / 0 / kal'mi");
        assert!(
            matches!(k, ErrorKind::InvalidHex) || matches!(k, ErrorKind::InvalidStructure(_)),
            "empty axis should be rejected"
        );
    }

    #[test]
    fn location_ebs_unbounded_and_decorator_trailing_only() {
        ok("0·0·0·0 / 0·0·0·0 / {10±FFFF}·{0...FFFFFFFFFFFFFFFF}~∞ / 00 / ANN / 0 / kal'mi");
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / ~⊥ 1·2 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidDecorator
        ));
    }

    #[test]
    fn non_hex_in_branch() {
        let k = err("A·1·1·1 / 0·0·0·0 / F / 00 / ANN / GHIJ / kal'mi");
        assert!(matches!(k, ErrorKind::InvalidHex));
    }

    #[test]
    fn branch_uppercase_normalization() {
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / beef / kal'mi");
        assert_eq!(branch_code(&c), "BEEF");
    }

    #[test]
    fn print_compacts_hex_except_fixed_width() {
        // Minute/second/tick compact; Tier stays 2-hex.
        let c = ok("A·0A·0·0 / 0·03·02·0000000F / 1·2 / 0A·0F / ANN / 0 / kal'mi");
        let out = format!("{c}");
        assert!(out.contains("A·A·0·0 / 0·3·2·F"));
        assert!(out.contains(" / 0A·0F / "));
    }

    #[test]
    fn whitespace_noise_and_round_trip() {
        let c = ok(
            "  aB·  ff · 0 · F  /  0 · 3f · 0 · f⟁  /  1 · 2 · 3 · 4 ~ ⊥  /  0a · ff  /  ANN · DRM / beef  /  kal'mi  ",
        );
        let out = format!("{c}");
        assert!(
            out.contains("AB·FF·0·F / 0·3F·0·F⟁ / 1·2·3·4~⊥ / 0A·FF / ANN·DRM / BEEF / kal'mi")
        );
    }

    #[test]
    fn round_trip_display_stability() {
        let s = "AB·FF·0·F / 0·3F·0·F⟁ / 1·2·3·4~⊥ / 0A·FF / ANN·DRM / BEEF / kal'mi";
        let c = ok(s);
        let out = format!("{c}");
        assert!(
            out.contains("AB·FF·0·F / 0·3F·0·F⟁ / 1·2·3·4~⊥ / 0A·FF / ANN·DRM / BEEF / kal'mi")
        );
    }

    #[test]
    fn only_middot_is_valid_separator_inside_segments() {
        assert!(matches!(
            err("0·0·0·0 / 0:0:0:0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    #[test]
    fn time_edges_exact_limits() {
        ok("0·00·0·0 / F·3F·3F·FFFFFFFF / 0 / 00 / ANN / 0 / kal'mi");
    }

    #[test]
    fn time_edges_reject_overflow() {
        assert!(matches!(
            err("0·00·0·0 / 10·0·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::OutOfRange("hour")
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·40·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::OutOfRange("minute")
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·40·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::OutOfRange("second")
        ));

        let k = err("0·00·0·0 / 0·0·0·100000000 / 0 / 00 / ANN / 0 / kal'mi");
        assert!(matches!(k, ErrorKind::InvalidHex) || matches!(k, ErrorKind::OutOfRange("tick")));
    }

    #[test]
    fn month_allows_leading_zero_two_hex() {
        ok("0·00·0A·0F / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi");
    }

    #[test]
    fn ebs_delta_and_range_checked() {
        assert!(matches!(
            err("0·00·0·0 / 0·{3F±FF}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::OutOfRange("minute")
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·{0...40}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::OutOfRange("minute")
        ));
    }

    #[test]
    fn minimal_minimal_ebs_mixed_values() {
        let c = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        assert!(matches!(c.date, Segment::Present(_)));
        assert!(matches!(c.time, Segment::Present(_)));
    }

    #[test]
    fn maximal_values() {
        let c = ok("FFFF·FF·F·F / F·3F·3F·FFFFFFFF / FFFF / FF / DRM / FFFF / ven'da");
        assert!(matches!(c.date, Segment::Present(_)));
        assert!(matches!(c.time, Segment::Present(_)));
    }

    #[test]
    fn ebs_plusminus_in_date() {
        let c = ok("A·{F±1}·{C±1}·{2±1} / 0·0·0·0 / F / 00 / ANN / 1 / kal'mi");
        assert!(matches!(c.date, Segment::Present(_)));
    }

    #[test]
    fn ebs_range_in_time() {
        let c =
            ok("A·1·1·1 / {F...F}·{0...3F}·{0...3F}·{0...FFFFFFFF} / F / 00 / ANN / 1 / kal'mi");
        assert!(matches!(c.time, Segment::Present(_)));
    }

    #[test]
    fn torture_long_and_complex() {
        let c = ok(
            "ABCDEF·FF·F·F / F·3F·3F·FFFFFFFF⟁ / 1·2·3·4·5·6·7·8~∞ / 0A·FF / ANN~·DRM~∂·NRV~⊥ / DEADCAFE / sarn'mi",
        );

        // time loop marker is a trailing annotation on the time segment
        match &c.time {
            Segment::Present(t) => assert!(matches!(t.loop_spec, Some(TimeLoop::Simple))),
            _ => panic!("time segment not present"),
        }

        let loc = match &c.location {
            Segment::Present(l) => l,
            _ => panic!("location not present"),
        };
        assert_eq!(loc.axes.len(), 8);

        let folds_len = match &c.folds {
            Segment::Present(f) => f.folds.len(),
            _ => panic!("folds not present"),
        };
        assert_eq!(folds_len, 3);
    }

    #[test]
    fn torture_whitespace_and_case() {
        let c = ok(
            "  abcd · ff · f · f  /  F · 3f · 3f · ffffffff  /  1 · 2 · 3 ~ ⊥  /  0a · FF  /  ANN · DRM  / beef  /  kal'mi  ",
        );
        let branch_code = match &c.branch {
            Segment::Present(b) => &b.code,
            _ => panic!("branch not present"),
        };
        assert_eq!(branch_code, "BEEF");
    }

    #[test]
    fn torture_many_axes_and_folds() {
        let c = ok(
            "1·2·3·4 / 0·0·0·0 / 1·2·3·4·5·6·7·8·9·A·B·C~∞ / 00 / ANN·DRM·NRV·SYM·PEN·TRM / DEADC0DE / vesh'da",
        );
        assert!(loc_axes(&c).len() >= 12);
        assert!(folds_vec(&c).len() >= 5);
    }

    #[test]
    fn dream_fold_tags_require_prior_drm_anywhere() {
        // Valid - dream tag after DRM (not necessarily adjacent).
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / DRM·LUC / 0 / kal'mi");
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·DRM·REMGEN / 0 / kal'mi");
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / DRM·ANN·LUC / 0 / kal'mi"); // Non-adjacent.

        // Multiple dream tags after a single DRM are fine.
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / DRM·LUC·INC·SYMDRM / 0 / kal'mi");

        // Valid - interleave with extra DRMs.
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / DRM·LUC·DRM·INC / 0 / kal'mi");

        // Invalid - first dream tag appears before any DRM.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / LUC / 0 / kal'mi"),
            ErrorKind::DreamFoldWithoutDrm
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·INC / 0 / kal'mi"),
            ErrorKind::DreamFoldWithoutDrm
        ));
    }

    #[test]
    fn inv_may_not_be_last_in_fold_chain() {
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / INV / 0 / kal'mi"),
            ErrorKind::InvAtEnd
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·INV / 0 / kal'mi"),
            ErrorKind::InvAtEnd
        ));

        // Valid _only_ when not last.
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / INV·ANN / 0 / kal'mi");
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / DRM·LUC·INV·REC / 0 / kal'mi");
    }

    #[test]
    fn dream_folds_with_decorators_and_prior_drm() {
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / DRM~∞·REMGEN~⊥·REC / 0 / kal'mi");
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / REMGEN~∂·REC / 0 / kal'mi"),
            ErrorKind::DreamFoldWithoutDrm
        ));
    }

    #[test]
    fn folds_accept_hex_codes_and_normalize() {
        let c = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / B7·DRM / 0 / kal'mi");
        if let Segment::Present(f) = c.folds {
            assert_eq!(f.folds[0].tag, "B7");
            assert_eq!(f.folds[1].tag, "DRM");
        } else {
            panic!()
        }

        // lowercase hex is accepted and uppercased
        let c = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ff·ANN / 0 / kal'mi");
        if let Segment::Present(f) = c.folds {
            assert_eq!(f.folds[0].tag, "FF");
            assert_eq!(f.folds[1].tag, "ANN");
        } else {
            panic!()
        }
    }

    #[test]
    fn folds_mixed_numeric_and_dream_with_prior_drm() {
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / B7·ANN·DRM·PSI / 0 / kal'mi");
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / DRM·FF·REMGEN / 0 / kal'mi");
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / B7·PSI / 0 / kal'mi"),
            ErrorKind::DreamFoldWithoutDrm
        ));
    }

    #[test]
    fn folds_hex_code_validation() {
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / F / 0 / kal'mi"),
            ErrorKind::InvalidFoldTag
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / 123 / 0 / kal'mi"),
            ErrorKind::InvalidFoldTag
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / G7 / 0 / kal'mi"),
            ErrorKind::InvalidFoldTag
        ));
    }

    #[test]
    fn inv_not_last_still_enforced_with_numeric_codes_present() {
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·INV / 0 / kal'mi"),
            ErrorKind::InvAtEnd
        ));
        // Ok when not last.
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / INV·B7 / 0 / kal'mi");
    }

    #[test]
    fn time_loop_variants_parse_and_print() {
        let c = ok("0·0·0·0 / 0·0·0·0⟁ / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = c.time {
            assert!(matches!(t.loop_spec, Some(TimeLoop::Simple)));
        } else {
            panic!();
        }

        let c = ok("0·0·0·0 / 0·0·0·0⟁∞ / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = c.time {
            assert!(matches!(t.loop_spec, Some(TimeLoop::Infinite)));
        } else {
            panic!();
        }

        let c = ok("0·0·0·0 / 0·0·0·0⟁∂ / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = c.time {
            assert!(matches!(t.loop_spec, Some(TimeLoop::UntilBoundary)));
        } else {
            panic!();
        }

        let c = ok("0·0·0·0 / 0·0·0·0⟁⊥ / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = c.time {
            assert!(matches!(t.loop_spec, Some(TimeLoop::Paradox)));
        } else {
            panic!();
        }

        let c = ok("0·0·0·0 / 0·0·0·0⟁A / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = &c.time {
            assert!(matches!(t.loop_spec, Some(TimeLoop::Count(10))));
        } else {
            panic!();
        }

        // Round-trip prints the suffix.
        let out = format!("{c}");
        assert!(out.contains("0·0·0·0⟁A"));
    }

    #[test]
    fn time_loop_bad_forms_are_rejected() {
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁0 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        )); // Zero not allowed, because a loop of zero makes no sense.

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁G / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0foo⟁A / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        assert!(matches!(
            err("0·0·0·0 / [selm]⟁A / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
    }

    #[test]
    fn vtfm_only_valid_dectorators() {
        let c = ok("0·0·0·0 / 0·0·0·0⪤↻ / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = c.time {
            assert!(matches!(t.vtfm, Some(TimeFlowMod::RecurringConvergence)));
        } else {
            panic!();
        }

        // P is not a valid dectorator for the VTFM.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⪤P / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::VtfmUnknownDecorator
        ));
    }

    #[test]
    fn vtfm_bare_and_with_loops() {
        // Bare ⪤ (non-linear flow), no loop.
        let c = ok("0·0·0·0 / 0·0·0·0⪤ / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = &c.time {
            assert!(matches!(t.vtfm, Some(TimeFlowMod::Nonlinear)));
            assert!(matches!(t.loop_spec, None));
        } else {
            panic!()
        }
        assert!(format!("{c}").contains("0·0·0·0⪤"));

        // Bare ⪤ + counted loop → prints ⪤⟁A (no duplication).
        let c = ok("0·0·0·0 / 0·0·0·0⪤⟁A / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = &c.time {
            assert!(matches!(t.vtfm, Some(TimeFlowMod::Nonlinear)));
            assert!(matches!(t.loop_spec, Some(TimeLoop::Count(0xA))));
        } else {
            panic!()
        }
        assert!(format!("{c}").contains("0·0·0·0⪤⟁A"));
    }

    #[test]
    fn vtfm_decorated_keeps_order_with_loop() {
        let c = ok("0·0·0·0 / 0·0·0·0⪤↻⟁∞ / 0 / 00 / ANN / 0 / kal");
        if let Segment::Present(t) = &c.time {
            assert!(matches!(t.vtfm, Some(TimeFlowMod::RecurringConvergence)));
            assert!(matches!(t.loop_spec, Some(TimeLoop::Infinite)));
        } else {
            panic!()
        }

        assert!(format!("{c}").contains("0·0·0·0⪤↻⟁∞"));
    }

    #[test]
    fn vtfm_only_at_end_and_only_once() {
        // Multiple VTFM.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⪤↻⪤⇌ / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::VtfmMisplaced
        ));

        // Stray ⪤ in the middle.
        assert!(matches!(
            err("0·0·0·0 / 0·0·⪤·0·0 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::VtfmUnknownDecorator
        ));
    }
}
