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
//! Returns a strongly typed [`Coordinate`] AST. Errors are categorised in [`ErrorKind`]
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
use once_cell::sync::Lazy;
use std::{borrow::Cow, collections::HashSet};

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

// Precomputed sets for O(1) membership checks.
static NORMAL_FOLDS: Lazy<HashSet<&'static str>> =
    Lazy::new(|| ALLOWED_FOLD_TAGS.iter().copied().collect());
static DREAM_FOLDS: Lazy<HashSet<&'static str>> =
    Lazy::new(|| ALLOWED_DREAM_FOLD_TAGS.iter().copied().collect());
static MODAL_TOKENS: Lazy<HashSet<&'static str>> =
    Lazy::new(|| ALLOWED_MODAL_TOKENS.iter().copied().collect());

/// Centralized VTFM mapping table - decorated suffix to enum.
const VTFM_SUFFIXES: &[(&str, TimeFlowMod)] = &[
    ("⪤↻", TimeFlowMod::RecurringConvergence),
    ("⪤⇌", TimeFlowMod::ReversibleOscillating),
    ("⪤⊞", TimeFlowMod::MultidirectionalBraided),
    ("⪤⊗", TimeFlowMod::CrossThreaded),
    ("⪤⊘", TimeFlowMod::VeiledFlux),
    ("⪤↡", TimeFlowMod::EntropicSink),
];

/// Allowed single-glyph decorators that may follow ⪤.
const VTFM_DECORATORS: &[&str] = &["↻", "⇌", "⊞", "⊗", "⊘", "↡"];

/// Top-level parse entry point.
pub fn parse(input: &str) -> Result<Coordinate, Error> {
    Parser::new(input).parse()
}

/// Recursion decorators permitted on Location (whole segment) and on Fold tags.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
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
    Count(u128),   // "⟁" + 1..8 hex digits, >= 1
}

/// Time segment - hour·minute·second·tick
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimeSegment {
    pub hour: ValueOrEbs<HexNum>,
    pub minute: ValueOrEbs<HexNum>,
    pub second: ValueOrEbs<HexNum>,
    pub tick: ValueOrEbs<HexNum>,
    pub vtfm: Option<TimeFlowMod>,
    pub loop_spec: Option<TimeLoop>,
}

/// Location segment - N axes (1+ hex digits each), and optional recursion decorator on the whole segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocationSegment {
    pub axes: Vec<ValueOrEbs<HexNum>>, // 1+ entries
    pub recursion: Recursion,
}

/// Dimensional tier - one or more elements, each exactly 2 hex digits (00..FF).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TierSegment {
    pub tiers: Vec<u8>,
}

/// Metaphysical Fold indices and tags, and optional recursion decorator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldTag {
    pub tag: String, // Uppercase 3 letters.
    pub recursion: Recursion,
}

/// Metaphysical Fold chain - 1 or more fold tags.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldsSegment {
    pub folds: Vec<FoldTag>,
}

/// Timeline branch segment - hex (1..=4 hex digits).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BranchSegment {
    pub code: String, // Normalised uppercase.
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
    InvalidHexValue(&'static str),
    EbsNotAllowedHere,
    UnbalancedBraces,
    InvalidEbsSyntax(&'static str),
    InvalidDecorator,
    InvalidFoldTag,
    LowercaseFoldTag,
    InvalidModalTruth,
    InvalidTimeLoopPlacement,
    TimeLoopCountTooLong,
    TimeLoopCountZero,
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
                f.write_str("wrong number of segments (expected exactly 7)")
            }
            ErrorKind::InvalidHex => f.write_str("invalid hexadecimal value"),
            ErrorKind::OutOfRange(label) => write!(f, "value out of range for {label}"),
            ErrorKind::InvalidHexValue(label) => write!(f, "invalid length for {label}"),
            ErrorKind::EbsNotAllowedHere => {
                f.write_str("EBS notation is not allowed in this segment")
            }
            ErrorKind::UnbalancedBraces => f.write_str("unbalanced braces in EBS notation"),
            ErrorKind::InvalidEbsSyntax(msg) => write!(f, "invalid EBS syntax: {msg}"),
            ErrorKind::InvalidDecorator => f.write_str("invalid decorator symbol or placement"),
            ErrorKind::InvalidFoldTag => f.write_str("invalid fold tag"),
            ErrorKind::LowercaseFoldTag => f.write_str("fold tags must be uppercase"),
            ErrorKind::InvalidModalTruth => f.write_str("invalid modal truth particle"),
            ErrorKind::InvalidTimeLoopPlacement => {
                f.write_str("invalid time-loop marker (⟁) placement")
            }
            ErrorKind::TimeLoopCountTooLong => {
                f.write_str("time-loop count has more than 8 hex digits")
            }
            ErrorKind::TimeLoopCountZero => f.write_str("time-loop count must be greater than 0"),
            ErrorKind::InvalidStructure(msg) => write!(f, "invalid structure: {msg}"),
            ErrorKind::DreamFoldWithoutDrm => {
                f.write_str("dream-fold tag requires a prior DRM tag in the fold chain")
            }
            ErrorKind::InvAtEnd => f.write_str("INV cannot be the last fold tag"),
            ErrorKind::VtfmMisplaced => f.write_str("invalid placement of vectorial time flow (⪤)"),
            ErrorKind::VtfmUnknownDecorator => {
                f.write_str("unknown vectorial time flow decorator after ⪤")
            }
            ErrorKind::VtfmMultiple => {
                f.write_str("multiple vectorial time flow modifiers are not allowed")
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

/// Hex number wrapper holding the normalised uppercase string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HexNum {
    pub text: String,
}

impl HexNum {
    fn parse_uppercased(s: &str) -> Result<Self, Error> {
        if s.is_empty() {
            return Err(Error::new(ErrorKind::InvalidHex, "empty"));
        }

        let up = s.to_ascii_uppercase();
        if !up.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(Error::new(ErrorKind::InvalidHex, s));
        }

        Ok(HexNum { text: up })
    }

    fn to_u128(&self) -> u128 {
        u128::from_str_radix(&self.text, 16).expect("validated hex")
    }
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

    fn split_dot(&self, s: &'a str) -> Vec<&'a str> {
        // DO NOT filter out empties; callers must validate them.
        s.split('·').map(str::trim).collect()
    }

    fn parse_recursion_suffix<'b>(&self, s: &'b str) -> Result<(Recursion, &'b str), Error> {
        let trimmed = s.trim_end();
        if let Some(pos) = trimmed.rfind('~') {
            let tail = trimmed[pos + 1..].trim();
            let rec = match tail {
                "" => Recursion::Tilde,
                "∞" => Recursion::TildeInf,
                "∂" => Recursion::TildePartial,
                "⊥" => Recursion::TildeBottom,
                _ => return Err(Error::new(ErrorKind::InvalidDecorator, &trimmed[pos..])),
            };

            let core = trimmed[..pos].trim_end();
            return Ok((rec, core));
        }

        Ok((Recursion::None, trimmed))
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
            return Err(Error::new(ErrorKind::InvalidHexValue(label), s));
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

        // No braces -> plain hex value.
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
        self.validate_upper_cap(&year, 0xFF, "year")?;

        let month = self.parse_value_or_ebs_hex(&parts[2])?;
        self.validate_upper_cap(&month, 0xF, "month")?;

        let day = self.parse_value_or_ebs_hex(&parts[3])?;
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

        // If we already consumed one VTFM, explicitly check if
        // another VTFM suffix remains at the end.
        if vtfm.is_some()
            && (VTFM_SUFFIXES.iter().any(|(s, _)| st.ends_with(*s)) || st.ends_with('⪤'))
        {
            return Err(Error::new(
                ErrorKind::VtfmMultiple,
                "more than one vectorial time flow modifier",
            ));
        }

        // Ensure there are no stray VTFM particles left behind.
        // That would be invalid syntax.
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
        // Allow trailing outer whitespace, but loop suffix itself must be contiguous.
        let st = s.trim_end();

        // Fixed forms first.
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

        // Hex-counted form - one trailing ⟁ followed by 1..8 *contiguous* hex digits.
        if let Some(pos) = st.rfind('⟁') {
            // Do NOT trim; spaces here are invalid.
            let tail_raw = &st[pos + '⟁'.len_utf8()..];
            if tail_raw.is_empty() {
                // Bare ⟁ at end would have matched above; reaching here means ⟁ not at absolute end.
                return Err(Error::new(
                    ErrorKind::InvalidTimeLoopPlacement,
                    "missing loop count after ⟁",
                ));
            }

            // A time-loop decorator must always come after a VTFM decorator.
            if tail_raw.contains('⪤') {
                return Err(Error::new(
                    ErrorKind::InvalidTimeLoopPlacement,
                    "a time-loop decorator before a VTFM decorator",
                ));
            }

            // Parse and reject zero explicitly.
            let h = self.parse_hex_with_len(tail_raw, 1, 8, "time_loop(1-8-hex)")?;
            let n = h.to_u128();
            if n == 0 {
                return Err(Error::new(ErrorKind::TimeLoopCountZero, tail_raw));
            }

            let head = st[..pos].trim_end();
            return Ok((head, Some(TimeLoop::Count(n))));
        }

        Ok((st, None))
    }

    /// Remove a single trailing VTFM marker from the end of `s` and return the prefix.
    /// Accepts bare `⪤` or decorated `⪤↻/⇌/⊞/⊗/⊘/↡`. Returns (remainder, vtfm_option).
    fn extract_vtfm_suffix<'b>(&self, s: &'b str) -> Result<(&'b str, Option<TimeFlowMod>), Error> {
        let mut st = s.trim_end();

        // Decorated VTFM particles first.
        for (pat, variant) in VTFM_SUFFIXES {
            if let Some(prefix) = st.strip_suffix(pat) {
                st = prefix.trim_end();
                return Ok((st, Some(variant.clone())));
            }
        }

        // And a bare VTFM particle if those fail.
        if st.ends_with('⪤') {
            let cut = &st[..st.len() - '⪤'.len_utf8()];
            return Ok((cut.trim_end(), Some(TimeFlowMod::Nonlinear)));
        }

        // If some ⪤ exists but not in a recognised suffix position.
        if let Some(pos) = st.rfind('⪤') {
            let tail = st[pos + '⪤'.len_utf8()..].trim_end();
            if !tail.is_empty() && !VTFM_DECORATORS.contains(&tail) {
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

        // Strip one trailing VTFM if present (decorated first).
        for (pat, _) in VTFM_SUFFIXES {
            if tick_preview.ends_with(pat) {
                tick_preview = tick_preview[..tick_preview.len() - pat.len()].trim_end();
                break;
            }
        }

        if tick_preview.ends_with('⪤') {
            tick_preview = tick_preview[..tick_preview.len() - '⪤'.len_utf8()].trim_end();
        }

        // If not an EBS token, it must look like ≤8 hex.
        if !tick_preview.contains('{')
            && !tick_preview.contains('}')
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
                return Err(Error::new(ErrorKind::InvalidHexValue("tier(2-hex)"), s));
            }

            let h = self.parse_hex_with_len(&p, 2, 2, "tier(2-hex)")?;
            tiers.push(h.to_u128() as u8);
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

            // The value may be a numeric fold code (00..FF).
            if tag.len() == 2 {
                let h = self.parse_hex_with_len(tag, 2, 2, "")?;
                folds.push(FoldTag {
                    tag: h.text.to_ascii_uppercase(),
                    recursion,
                });
                continue;
            }

            // Tags should only ever be in uppercase (symbolic tags).
            if tag.is_empty() || !tag.chars().all(|c| c.is_ascii_uppercase()) {
                if tag.chars().any(|c| c.is_ascii_lowercase()) {
                    return Err(Error::new(ErrorKind::LowercaseFoldTag, tag));
                }

                return Err(Error::new(ErrorKind::InvalidFoldTag, tag));
            }

            let is_normal = NORMAL_FOLDS.contains(tag);
            let is_dream = DREAM_FOLDS.contains(tag);

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
            && last.tag == "INV"
        {
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
        let trimmed = s.trim();
        let st: Cow<'_, str> = if trimmed.contains('\u{2019}') {
            Cow::Owned(trimmed.replace('\u{2019}', "'"))
        } else {
            Cow::Borrowed(trimmed)
        };

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
                (&st, "")
            };

        // Optional inversion prefix "na'" ONLY at the beginning, no spaces, only once.
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
        if !MODAL_TOKENS.contains(token_str) {
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
        write!(f, "{} / ", display_segment(&self.time, display_time))?;
        write!(
            f,
            "{} / ",
            display_segment(&self.location, display_location)
        )?;
        write!(f, "{} / ", display_segment(&self.tier, display_tier))?;
        write!(f, "{} / ", display_segment(&self.folds, display_folds))?;
        write!(f, "{} / ", display_segment(&self.branch, display_branch))?;
        write!(f, "{}", display_segment(&self.modal, display_modal))?;
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
            TimeLoop::Count(n) => out.push_str(&format!("⟁{n:X}")),
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

    // -----------------------
    // Helpers
    // -----------------------

    fn ok(input: &str) -> Coordinate {
        parse(input).expect("should parse")
    }

    fn err(input: &str) -> ErrorKind {
        match parse(input) {
            Ok(_) => panic!("expected error"),
            Err(e) => e.kind,
        }
    }

    fn time(c: &Coordinate) -> &TimeSegment {
        match &c.time {
            Segment::Present(t) => &t,
            _ => panic!("time not present"),
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

    // -----------------------
    // Structure & separators
    // -----------------------

    #[test]
    fn requires_exactly_7_segments_and_no_empty_segment() {
        assert!(matches!(
            err("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7"),
            ErrorKind::WrongSegmentCount
        ));

        assert!(matches!(
            err("A·0·0·0 / 0·0·0·0 / F / 00 / ANN / B7 / kal'mi / extra"),
            ErrorKind::WrongSegmentCount
        ));

        assert!(matches!(
            err("A·0·0·0 / 0·0·0·0 /  / 00 / ANN / B7 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    #[test]
    fn only_middot_as_inner_separator() {
        // Bad - colon
        assert!(matches!(
            err("0·0·0·0 / 0:0:0:0 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidStructure(_)
        ));

        // Bad - bullet lookalike.
        assert!(matches!(
            err("0·0·0·0 / 0•0•0•0 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    // -----------------------
    // Happy path (with VTFM & loop)
    // -----------------------

    #[test]
    fn parses_full_example_with_vtfm_and_loop() {
        let s = "12BFF·7·D·A / 3·1F·2A·FF⪤↻⟁A / 3·9·1C·1A~∞ / D2·A1 / ANN·DRM / B7C5 / kal'mi";
        let c = ok(s);
        match &c.time {
            Segment::Present(t) => {
                assert!(matches!(t.vtfm, Some(TimeFlowMod::RecurringConvergence)));
                assert!(matches!(t.loop_spec, Some(TimeLoop::Count(0xA))));
            }
            _ => panic!("time not present"),
        }
        assert!(matches!(c.tier, Segment::Present(_)));
        assert!(matches!(c.folds, Segment::Present(_)));
        assert!(matches!(c.branch, Segment::Present(_)));
        assert!(matches!(c.modal, Segment::Present(_)));
    }

    // -----------------------
    // Time-loop - placement, forms, counts
    // -----------------------

    #[test]
    fn loop_marker_misplacement_and_standalone() {
        // Standalone or outside time segment.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / ⟁ / 00 / ANN / 1 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / ⟁ / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        // Not at end of time / doubled.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁⟁ / 0 / 00 / ANN / 1 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        // Placeholder with loop.
        assert!(matches!(
            err("0·0·0·0 / [selm]⟁ / 0 / 00 / ANN / 1 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));

        assert!(matches!(
            err("0·0·0·0 / [veth]⟁A / 0 / 00 / ANN / 1 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
    }

    #[test]
    fn loop_valid_forms_and_counts() {
        ok("0·0·0·0 / 0·0·0·0⟁ / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁∞ / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁∂ / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁⊥ / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁1 / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·0⟁A / 0 / 00 / ANN / 0 / kal");

        // Up to a max of 8 hex digits.
        ok("0·0·0·0 / 0·0·0·0⟁FFFFFFFF / 0 / 00 / ANN / 0 / kal");
    }

    #[test]
    fn loop_bad_counts_and_spaces() {
        // Zero or too long or space-split.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁0 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::TimeLoopCountZero
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁00000000 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::TimeLoopCountZero
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁123456789 / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidHexValue("time_loop(1-8-hex)")
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁ A / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidHex
        ));
    }

    #[test]
    fn loop_with_ebs_tick_and_vtfm_preflight() {
        ok("0·0·0·0 / 0·0·0·{FF}⪤⟁A / 0 / 00 / ANN / 0 / kal");
        ok("0·0·0·0 / 0·0·0·{1±2}⪤↻⟁∞ / 0 / 00 / ANN / 0 / kal");

        // Junk before loop particle = placement error (not generic hex).
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0foo⟁A / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement
        ));
    }

    // -----------------------
    // VTFM - placement, variants
    // -----------------------

    #[test]
    fn vtfm_bare_and_decorated_and_with_loop() {
        // Bare.
        let c = ok("0·0·0·0 / 0·0·0·0⪤ / 0 / 00 / ANN / 0 / kal");
        match c.time {
            Segment::Present(t) => assert!(matches!(t.vtfm, Some(TimeFlowMod::Nonlinear))),
            _ => panic!("time not present"),
        }

        // Decorated + loop.
        let c = ok("0·0·0·0 / 0·0·0·0⪤↻⟁A / 0 / 00 / ANN / 0 / kal");
        match &c.time {
            Segment::Present(t) => {
                assert!(matches!(t.vtfm, Some(TimeFlowMod::RecurringConvergence)));
                assert!(matches!(t.loop_spec, Some(TimeLoop::Count(0xA))));
            }
            _ => panic!("time not present"),
        }

        // Display order - VTFM then loop.
        assert!(format!("{c}").contains("0·0·0·0⪤↻⟁A"));
    }

    #[test]
    fn vtfm_misplacement_and_errors() {
        // Unknown decorator.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⪤? / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::VtfmUnknownDecorator
        ));

        // Multiple.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⪤↻⪤⇌ / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::VtfmMultiple
        ));

        // Misplaced outside time.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 1·2·3·4⪤↻ / 00 / ANN / 0 / kal"),
            ErrorKind::VtfmMisplaced
        ));

        // After loop (wrong order).
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⟁A⪤↻ / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidTimeLoopPlacement | ErrorKind::VtfmMisplaced
        ));

        // Sub-secting space.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0⪤ ↻ / 0 / 00 / ANN / 0 / kal"),
            ErrorKind::VtfmUnknownDecorator | ErrorKind::VtfmMisplaced
        ));
    }

    // -----------------------
    // Time bounds & edges
    // -----------------------

    #[test]
    fn time_edges_limits_and_overflow() {
        // Exact edges allowed.
        ok("0·00·0·0 / F·3F·3F·FFFFFFFF / 0 / 00 / ANN / 0 / kal'mi");

        // Overflow rejects.
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

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·100000000 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidHex | ErrorKind::OutOfRange("tick")
        ));
    }

    // -----------------------
    // EBS rules
    // -----------------------

    #[test]
    fn ebs_allowed_only_in_date_time_location() {
        ok("A·FF·{A±1}·{B...D} / 0·{3E±1}·2·1 / {10±2}·20·30 / 00 / ANN / B7 / kal'mi");
        assert!(matches!(
            err("A·FF·0·0 / 0·0·0·0 / F / {0A} / ANN / B7 / kal'mi"),
            ErrorKind::EbsNotAllowedHere
        ));

        assert!(matches!(
            err("A·FF·0·0 / 0·0·0·0 / F / 0A / ANN / {BEEF} / kal'mi"),
            ErrorKind::EbsNotAllowedHere
        ));

        assert!(matches!(
            err("A·FF·0·0 / 0·0·0·0 / F / 0A / ANN / BEEF / {kal'mi}"),
            ErrorKind::EbsNotAllowedHere
        ));
    }

    #[test]
    fn ebs_unbalanced_and_malformed_and_nesting() {
        // Unbalanced.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·{FF / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::UnbalancedBraces
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·FF} / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::UnbalancedBraces
        ));

        // Must wrap whole token.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·A{FF} / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        // Empty.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·{} / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        // ± must have both sides.
        assert!(matches!(
            err("0·00·0·0 / 0·{±1}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·{3F±}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        // ... must have both.
        assert!(matches!(
            err("0·00·0·0 / 0·{...3F}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·{3F...}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        // Nested EBS invalid.
        assert!(matches!(
            err("0·00·0·0 / 0·{{3}±1}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::InvalidEbsSyntax(_)
        ));

        // Valid EBS with inner whitespace.
        ok("0·00·0·0 / 0·{3E ± 1}·{2 ... 3}·{0FFFFFFF} / 0 / 00 / ANN / 0 / kal'mi");
    }

    #[test]
    fn ebs_caps_upper_endpoint_only() {
        // ± - minute center+delta <= 0x3F.
        ok("0·00·0·0 / 0·{3E±1}·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        assert!(matches!(
            err("0·00·0·0 / 0·{2±3E}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::OutOfRange("minute")
        ));

        // Range - end <= 0x3F.
        ok("0·00·0·0 / 0·{0...3F}·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        assert!(matches!(
            err("0·00·0·0 / 0·{0...40}·0·0 / 0 / 00 / ANN / 0 / kal'mi"),
            ErrorKind::OutOfRange("minute")
        ));
    }

    #[test]
    fn location_ebs_unbounded_and_decorator_trailing_only() {
        ok("0·0·0·0 / 0·0·0·0 / {10±FFFF}·{0...FFFFFFFFFFFFFFFF}·3~∞ / 00 / ANN / 0 / kal");
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / ~⊥ 1·2 / 00 / ANN / 0 / kal"),
            ErrorKind::InvalidDecorator
        ));
    }

    // -----------------------
    // Location & many axes
    // -----------------------

    #[test]
    fn location_many_axes_and_whitespace_tolerant_decorator() {
        let c1 = ok("0·00·0·0 / 0·0·0·0 / 1·2·3~⊥ / 00 / ANN / 0 / kal");
        assert_eq!(loc_axes(&c1).len(), 3);

        let c2 = ok("0·00·0·0 / 0·0·0·0 / 1·2·3 ~⊥ / 00 / ANN / 0 / kal");
        assert_eq!(loc_axes(&c2).len(), 3);

        let c3 = ok("0·00·0·0 / 0·0·0·0 / 1·2·3~ ⊥ / 00 / ANN / 0 / kal");
        assert_eq!(loc_axes(&c3).len(), 3);
    }

    // -----------------------
    // Dimensional Tier
    // -----------------------

    #[test]
    fn tier_exactly_two_hex_and_chain() {
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 0A·FF·01 / ANN / 1 / ven'da");
        if let Segment::Present(t) = c.tier {
            assert_eq!(t.tiers, vec![0x0A, 0xFF, 0x01]);
        }

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / A / ANN / 1 / ven'da"),
            ErrorKind::InvalidHexValue("tier(2-hex)")
        ));

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 0AF / ANN / 1 / ven'da"),
            ErrorKind::InvalidHexValue("tier(2-hex)")
        ));

        // EBS not allowed in tier.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / {0A} / ANN / 1 / ven'da"),
            ErrorKind::EbsNotAllowedHere
        ));
    }

    // -----------------------
    // Metaphysical Folds
    // -----------------------

    #[test]
    fn folds_uppercase_allowlist_and_indices() {
        ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN·REC / B7 / kal");

        // Numeric indices uppercase normalised.
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN·0a·DRM·FF / B7 / kal");
        let folds = folds_vec(&c);

        // We just assert chain length and that numeric items remain present;
        // internal normalisation is implementation detail.
        assert_eq!(folds.len(), 4);

        // Hex numbers of length other than 2 should be rejected.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / A / B7 / kal"),
            ErrorKind::InvalidFoldTag
        ));
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / AAAA / B7 / kal"),
            ErrorKind::InvalidFoldTag
        ));

        // Hex numbers with a space should be rejected.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / A A / B7 / kal"),
            ErrorKind::InvalidFoldTag
        ));

        // Lowercase tag rejected.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / ann / B7 / kal"),
            ErrorKind::LowercaseFoldTag
        ));

        // Unknown tag rejected.
        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / XYZ / B7 / kal"),
            ErrorKind::InvalidFoldTag
        ));

        // Empty fold item rejected.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN··REC / 0 / kal"),
            ErrorKind::InvalidFoldTag
        ));
    }

    #[test]
    fn dreamfold_tags_require_prior_drm_and_inv_not_last() {
        // Needs DRM before dreamfold tags like PSI, CRY, ...
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·PSI / 0 / kal"),
            ErrorKind::DreamFoldWithoutDrm
        ));
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·DRM·PSI / 0 / kal");

        // INV cannot be last.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·DRM·INV / 0 / kal"),
            ErrorKind::InvAtEnd
        ));

        // DRM gating still holds if DRM appears earlier than the dreamfold tag.
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN·INV·DRM·PSI / 0 / kal");
    }

    // -----------------------
    // Timeline Branch
    // -----------------------

    #[test]
    fn branch_hex_normalisation_and_rejection_of_non_hex() {
        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / beef / kal'mi");
        assert_eq!(branch_code(&c), "BEEF");

        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / kal'mi");
        assert_eq!(branch_code(&c), "0");

        let c = ok("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / DEADBEEF / kal'mi");
        assert_eq!(branch_code(&c), "DEADBEEF");

        assert!(matches!(
            err("0·00·0·0 / 0·0·0·0 / 0 / 00 / ANN / GHIJ / kal'mi"),
            ErrorKind::InvalidHex
        ));
    }

    // -----------------------
    // Modal truth (raw tokens, suffixes, inversion, apostrophes, brackets)
    // -----------------------

    #[test]
    fn modal_suffix_token_inversion_and_raw_token() {
        // Suffix variants.
        let c = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / dūl'da");
        if let Segment::Present(m) = c.modal {
            assert_eq!(m.token, "dūl");
            assert_eq!(m.suffix, "'da");
            assert!(!m.inverted);
        }

        // Raw token (divine absolute).
        let c = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / kal");
        if let Segment::Present(m) = c.modal {
            assert_eq!(m.token, "kal");
            assert_eq!(m.suffix, ""); // Raw, no suffix.
        }

        // Inversion.
        let c = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na'kal'mi");
        if let Segment::Present(m) = c.modal {
            assert!(m.inverted);
            assert_eq!(m.token, "kal");
            assert_eq!(m.suffix, "'mi");
        }

        // Internal apostrophe stays, curly suffix canonicalised.
        let c = ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / inther'kael’mi");
        if let Segment::Present(m) = c.modal {
            assert_eq!(m.token, "inther'kael");
            assert_eq!(m.suffix, "'mi");
        }
    }

    #[test]
    fn modal_misuse_and_brackets_and_veiling() {
        // Unknown token.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / nope'da"),
            ErrorKind::InvalidModalTruth
        ));

        // "na'" only at start, no spaces.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / kal'na'mi"),
            ErrorKind::InvalidModalTruth
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na' kal'mi"),
            ErrorKind::InvalidModalTruth
        ));

        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 1 / na'na'kal'mi"),
            ErrorKind::InvalidModalTruth
        ));

        // Modal is not bracketed.
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / [kal'mi]"),
            ErrorKind::InvalidStructure(_)
        ));

        // Veil ok, omit not ok.
        ok("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / [selm]");
        assert!(matches!(
            err("0·0·0·0 / 0·0·0·0 / 0 / 00 / ANN / 0 / [veth]"),
            ErrorKind::InvalidStructure(_)
        ));
    }

    // -----------------------
    // Round-trip & canonicalisation
    // -----------------------

    #[test]
    fn round_trip_canonicalises_noise_and_is_stable() {
        let noisy = "  abcd · ff · f · f  /  F · 3f · 3f · ffffffff⪤↻⟁a  /  1 · 2 · 3 ~ ⊥  /  0a · FF  /  ANN · REC  / beef  /  kal'mi  ";
        let out = format!("{}", ok(noisy));
        assert!(out.contains(
            "ABCD·FF·F·F / F·3F·3F·FFFFFFFF⪤↻⟁A / 1·2·3~⊥ / 0A·FF / ANN·REC / BEEF / kal'mi"
        ));

        // Stable print on second round.
        assert_eq!(out, format!("{}", ok(&out)));
    }

    // -----------------------
    // Misc placeholders
    // -----------------------

    #[test]
    fn placeholders_keep_structure_and_time_placeholders_ok() {
        ok("[selm] / [veth] / [selm] / [veth] / ANN / 0 / kal'mi");
        assert!(matches!(
            err("[selm] / [veth] / [selm] /  / ANN / 0 / kal'mi"),
            ErrorKind::InvalidStructure(_)
        ));

        ok("0·0·0·0 / [selm] / 0 / 00 / ANN / 0 / kal'mi");
        ok("0·0·0·0 / [veth] / 0 / 00 / ANN / 0 / kal'mi");
    }

    // -----------------------
    // Torture tests
    // -----------------------

    #[test]
    fn gargantuan_coordinate_all_supported_features_including_vtfm_and_loop() {
        // Date: large cycle + nontrivial Y/M/D.
        // Time: max tick + decorated VTFM (⪤⊗ CrossThreaded) + counted loop (8 hex digits).
        // Location: exercises all EBS kinds in input (range, ±, exact), plus plain values, plus recursion ~⊥.
        // Tier: long chain of 2-hex tiers.
        // Folds: normal + numeric index + DRM-gated dreamfolds + chain tags (INV not last).
        // Branch: arbitrarily long hex (no length cap).
        // Modal: inverted token with curly apostrophes normalised.
        let s = "\
            12BFF·7·D·A \
            / F·3F·3F·FFFFFFFF⪤⊗⟁7F3A2C1D \
            / {0...FFFFFFFFFFFFFFFF}·{10±FFFF}·{0000000F}·1·2·3E·4D·{3E ± 1}·{2 ... 3}·7·8·9~⊥ \
            / 00·01·0A·FF·D2·A1 \
            / ANN·0F·DRM·REMGEN·LUC·PSI·REC·INV·RLK·SPR·SYM·TMP \
            / DEADBEEFCAFEBABE0123456789ABCDEF \
            / na’inther'kael’da";

        let c = ok(s);

        let t = time(&c);
        assert!(
            matches!(t.vtfm, Some(TimeFlowMod::CrossThreaded)),
            "expected ⪤⊗ to map to CrossThreaded"
        );

        assert!(matches!(t.loop_spec, Some(TimeLoop::Count(0x7F3A2C1D))));

        let rendered = format!("{c}");
        assert!(
            rendered.contains(" / F·3F·3F·FFFFFFFF⪤⊗⟁7F3A2C1D / "),
            "rendered={rendered}"
        );

        match &c.location {
            Segment::Present(loc) => {
                assert_eq!(loc.axes.len(), 12);

                // We don't match inner EBS variant names; just assert EBS is used where intended.
                assert!(
                    matches!(loc.axes[0], ValueOrEbs::Ebs(_)),
                    "axis 0 should be EBS (range)"
                );

                assert!(
                    matches!(loc.axes[1], ValueOrEbs::Ebs(_)),
                    "axis 1 should be EBS (±)"
                );

                assert!(
                    matches!(loc.axes[2], ValueOrEbs::Ebs(_)),
                    "axis 2 should be EBS (exact)"
                );

                assert!(matches!(loc.recursion, Recursion::TildeBottom));
            }
            _ => panic!("location not present"),
        }

        if let Segment::Present(tier) = &c.tier {
            assert_eq!(tier.tiers, vec![0x00, 0x01, 0x0A, 0xFF, 0xD2, 0xA1]);
        } else {
            panic!("tier not present");
        }

        let f = folds_vec(&c);
        assert!(f.len() >= 10);
        assert!(
            rendered.contains("/ ANN·0F·DRM·REMGEN·LUC·PSI·REC·INV·RLK·SPR"),
            "rendered={rendered}"
        );

        assert_eq!(branch_code(&c), "DEADBEEFCAFEBABE0123456789ABCDEF");

        if let Segment::Present(m) = &c.modal {
            assert!(m.inverted);
            assert_eq!(m.token, "inther'kael");
            assert_eq!(m.suffix, "'da");
        } else {
            panic!("modal not present");
        }

        let canon = format!("{c}");
        let c2 = ok(&canon);
        assert_eq!(format!("{c2}"), canon);
    }
}
