use std::num::{NonZeroU8, ParseIntError};

#[derive(Debug, Eq, PartialEq)]
pub struct ExpandedCode(Vec<Code>);

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Address([u8; 3]);
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct AddressDelta(pub NonZeroU8);
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ValueDelta(pub i16);
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct RepeatCount(pub NonZeroU8);

pub type RawCodeLine = (u32, u16);

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum SingleCodeType {
    Write8,
    Write16,
    Once8,
    Once16,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SingleCode {
    Write8(Address, u8),
    Write16(Address, u16),
    Once8(Address, u8),
    Once16(Address, u16),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum CompositeCode {
    Check8(Address, u8, SingleCode),
    Check16(Address, u16, SingleCode),
    Repeat(RepeatCount, AddressDelta, ValueDelta, SingleCode),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Code {
    Single(SingleCode),
    Composite(CompositeCode),
}

impl ExpandedCode {
    pub fn get(&self) -> &Vec<Code> {
        &self.0
    }
}

impl Address {
    pub fn get(&self) -> u32 {
        (self.0[0] as u32) << 16 | (self.0[1] as u32) << 8 | (self.0[2] as u32) | 0x8000_0000
    }
}

impl SingleCodeType {
    pub fn value_mask(self) -> u16 {
        match self {
            SingleCodeType::Once8 | SingleCodeType::Write8 => 0xFF,
            SingleCodeType::Once16 | SingleCodeType::Write16 => 0xFFFF,
        }
    }
}

impl SingleCode {
    pub fn code_type(self) -> SingleCodeType {
        use SingleCode::*;

        match self {
            Write8(_, _) => SingleCodeType::Write8,
            Write16(_, _) => SingleCodeType::Write16,
            Once8(_, _) => SingleCodeType::Once8,
            Once16(_, _) => SingleCodeType::Once16,
        }
    }

    pub fn code_byte(self) -> u8 {
        use SingleCode::*;

        match self {
            Write8(_, _) => 0x80,
            Write16(_, _) => 0x81,
            Once8(_, _) => 0xD0,
            Once16(_, _) => 0xD1,
        }
    }
    pub fn rhs(self) -> u16 {
        use SingleCode::*;

        match self {
            Write8(_, v) => v as u16,
            Write16(_, v) => v,
            Once8(_, v) => v as u16,
            Once16(_, v) => v,
        }
    }

    pub fn affected_address(self) -> u32 {
        use SingleCode::*;

        match self {
            Write8(a, _) | Write16(a, _) | Once8(a, _) | Once16(a, _) => a.get(),
        }
    }

    pub fn nth_repetition(self, n: u32, da: AddressDelta, dv: ValueDelta) -> SingleCode {
        use SingleCode::*;

        let mk_addr = |a: Address| make_address(n * (da.0.get() as u32) + a.get());

        let mk_val = |v: u16| (v as i16 as i32 + dv.0 as i32 * n as i32) as i16 as u16;

        match self {
            Write8(a, v) => Write8(mk_addr(a), mk_val(v as u16) as u8),
            Write16(a, v) => Write16(mk_addr(a), mk_val(v)),
            Once8(a, v) => Once8(mk_addr(a), mk_val(v as u16) as u8),
            Once16(a, v) => Once16(mk_addr(a), mk_val(v)),
        }
    }
}

impl Code {
    pub fn is_single(&self) -> bool {
        match self {
            Code::Single(_) => true,
            _ => false,
        }
    }

    pub fn is_composite(&self) -> bool {
        !self.is_single()
    }

    pub fn affected_address(&self) -> u32 {
        match self {
            Code::Single(x) => x.affected_address(),
            Code::Composite(x) => match x {
                CompositeCode::Repeat(_, _, _, x)
                | CompositeCode::Check8(_, _, x)
                | CompositeCode::Check16(_, _, x) => x.affected_address(),
            },
        }
    }
}

pub use code_fmt::CodeDisplay;
use std::collections::BTreeMap;

mod code_fmt {
    use super::{Code, CompositeCode, SingleCode};
    use crate::gs::RawCodeLine;
    use std::fmt::{Display, Error, Formatter};

    pub struct PrintCode<T>(T);

    pub trait CodeDisplay
    where
        Self: AsRef<[<Self as CodeDisplay>::Code]>,
    {
        type Code;

        fn fmt(&self) -> PrintCode<&[Self::Code]> {
            PrintCode(self.as_ref())
        }
    }

    impl<C> CodeDisplay for [C] {
        type Code = C;
    }
    impl<C> CodeDisplay for Vec<C> {
        type Code = C;
    }
    impl<'a, T: ?Sized> CodeDisplay for &'a T
    where
        T: CodeDisplay,
    {
        type Code = <T as CodeDisplay>::Code;
    }

    impl<C> Display for PrintCode<C>
    where
        C: CodeDisplay,
        C::Code: Display,
    {
        fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
            for x in self.0.as_ref() {
                writeln!(f, "{}", x)?;
            }

            Ok(())
        }
    }

    impl Display for SingleCode {
        fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
            let (addr, val) = match self {
                SingleCode::Write8(a, v) => (0x80000000 | a.get(), *v as u16),
                SingleCode::Write16(a, v) => (0x81000000 | a.get(), *v),
                SingleCode::Once8(a, v) => (0xA0000000 | a.get(), *v as u16),
                SingleCode::Once16(a, v) => (0xA1000000 | a.get(), *v),
            };

            write!(f, "{:08X} {:04X}", addr, val)
        }
    }

    impl Display for Code {
        fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
            fn write_composite(
                f: &mut Formatter,
                line: RawCodeLine,
                other: &SingleCode,
            ) -> Result<(), Error> {
                writeln!(f, "{:08X} {:04X}", line.0, line.1)?;
                other.fmt(f)
            }

            match self {
                Code::Single(x) => x.fmt(f),
                Code::Composite(c) => match c {
                    CompositeCode::Repeat(count, da, dv, r) => write_composite(
                        f,
                        (
                            0x50000000 | (count.0.get() as u32) << 8 | (da.0.get() as u32),
                            dv.0 as u16,
                        ),
                        r,
                    ),
                    CompositeCode::Check8(a, v, c) => {
                        write_composite(f, (0xD0000000 | a.get(), *v as u16), c)
                    }
                    CompositeCode::Check16(a, v, c) => {
                        write_composite(f, (0xD1000000 | a.get(), *v), c)
                    }
                },
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum GsSingleError {
    UnknownCodeType(u8),
}

#[derive(Debug, Eq, PartialEq)]
pub enum GsCodeError {
    SingleError(RawCodeLine, GsSingleError),
    CompositeEof(RawCodeLine),
    CompositeError(RawCodeLine, RawCodeLine, GsSingleError),
    InvalidRepeatCount(RawCodeLine),
    InvalidAddressDelta(RawCodeLine),
}

#[derive(Debug, Eq, PartialEq)]
pub enum GsStrError {
    AddressError(usize, String, ParseIntError),
    ValueError(usize, String, ParseIntError),
    AddressMissing(usize, String),
    ValueMissing(usize, String),
    Code(GsCodeError),
}

pub(crate) fn make_address(addr: u32) -> Address {
    Address([(addr >> 16) as u8, (addr >> 8) as u8, addr as u8])
}

fn interp_single(code: RawCodeLine) -> Result<SingleCode, GsSingleError> {
    use SingleCode::*;

    let (addr, val) = code;
    let kind = addr >> 24;
    let addr = make_address(addr);

    Ok(match kind {
        0x80 => Write8(addr, val as u8),
        0x81 => Write16(addr, val),
        0xA0 => Once8(addr, val as u8),
        0xA1 => Once16(addr, val),
        x => return Err(GsSingleError::UnknownCodeType(x as u8)),
    })
}

pub fn interp_codes(raw: &[RawCodeLine]) -> Result<Vec<Code>, GsCodeError> {
    use Code::*;
    use CompositeCode::*;

    let mut codes = Vec::new();
    let mut skip_next = false;

    for (i, &line) in raw.iter().enumerate() {
        if skip_next {
            skip_next = false;
            continue;
        }

        let (addr, val) = line;
        let kind = addr >> 24;
        let cur_code = interp_single(line);
        let next_raw = raw.get(i + 1);
        let next_code = next_raw.map(|&x| interp_single(x));
        let address = make_address(addr);

        codes.push(match (kind, cur_code, next_raw, next_code) {
            (_, Ok(x), _, _) => Single(x),
            (0x50, _, _, Some(Ok(x))) => Composite(Repeat(
                RepeatCount(
                    NonZeroU8::new((addr >> 8) as u8)
                        .ok_or(GsCodeError::InvalidRepeatCount(line))?,
                ),
                AddressDelta(
                    NonZeroU8::new(addr as u8).ok_or(GsCodeError::InvalidAddressDelta(line))?,
                ),
                ValueDelta(val as i16),
                x,
            )),
            (0xD0, _, _, Some(Ok(x))) => Composite(Check8(address, val as u8, x)),
            (0xD1, _, _, Some(Ok(x))) => Composite(Check16(address, val, x)),
            (0x50, _, None, _) | (0xD0, _, None, _) | (0xD1, _, None, _) => {
                return Err(GsCodeError::CompositeEof(line))
            }
            (0x50, _, Some(x), Some(Err(e)))
            | (0xD0, _, Some(x), Some(Err(e)))
            | (0xD1, _, Some(x), Some(Err(e))) => {
                return Err(GsCodeError::CompositeError(line, *x, e))
            }
            (_, Err(x), _, _) => return Err(GsCodeError::SingleError(line, x)),
        });

        skip_next = codes.last().map(Code::is_composite) == Some(true);
    }

    Ok(codes)
}

pub fn from_str(s: &str) -> Result<Vec<Code>, GsStrError> {
    let mut lines = Vec::new();

    for (line_no, l) in s.lines().enumerate() {
        let l = l.trim();

        if l.len() == 0 {
            continue;
        }

        let mut addr = None;
        let mut val = None;

        for (i, p) in l.split(' ').enumerate() {
            match i {
                0 => {
                    addr = Some(
                        u32::from_str_radix(p, 16)
                            .map_err(|e| GsStrError::AddressError(line_no, l.to_owned(), e))?,
                    )
                }
                1 => {
                    val = Some(
                        u16::from_str_radix(p, 16)
                            .map_err(|e| GsStrError::ValueError(line_no, l.to_owned(), e))?,
                    )
                }
                _ => {}
            }
        }

        match (addr, val) {
            (None, _) => return Err(GsStrError::AddressMissing(line_no, l.to_owned())),
            (_, None) => return Err(GsStrError::ValueMissing(line_no, l.to_owned())),
            (Some(addr), Some(val)) => lines.push((addr, val)),
        }
    }

    interp_codes(&lines).map_err(|e| GsStrError::Code(e))
}

pub fn expand_code(code: &[Code]) -> ExpandedCode {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
    enum ByteType {
        Once,
        Write,
    }

    let (ignored, mem) = code
        .iter()
        .cloned()
        .flat_map(|x| match x {
            Code::Composite(CompositeCode::Repeat(count, da, dv, repeated)) => (0..count.0.get())
                .map(|i| Code::Single(repeated.nth_repetition(i as u32, da, dv)))
                .collect::<Vec<_>>(),
            x => vec![x],
        })
        .fold(
            (Vec::new(), BTreeMap::new()),
            |(mut ignored, mut mem), cur| {
                match &cur {
                    Code::Composite(_) => ignored.push(cur),
                    Code::Single(x) => {
                        let byte_type = match x.code_type() {
                            SingleCodeType::Once8 | SingleCodeType::Once16 => ByteType::Once,
                            SingleCodeType::Write8 | SingleCodeType::Write16 => ByteType::Write,
                        };

                        match x {
                            SingleCode::Once8(addr, v) | SingleCode::Write8(addr, v) => {
                                *mem.entry((byte_type, addr.get())).or_insert(0) = *v
                            }
                            SingleCode::Once16(addr, v) | SingleCode::Write16(addr, v) => {
                                let addr = addr.get();
                                *mem.entry((byte_type, addr)).or_insert(0) = (*v >> 8) as u8;
                                *mem.entry((byte_type, addr + 1)).or_insert(0) = *v as u8;
                            }
                        }
                    }
                }

                (ignored, mem)
            },
        );

    let count = mem.len();
    let mut final_code = mem
        .into_iter()
        .enumerate()
        .fold(
            (Vec::new(), Option::<(u32, u8)>::None),
            |(mut result, prev), (i, ((code_type, addr), val))| {
                let make_8 = |addr: u32, val: u8| {
                    Code::Single(match code_type {
                        ByteType::Once => SingleCode::Once8(make_address(addr), val),
                        ByteType::Write => SingleCode::Write8(make_address(addr), val),
                    })
                };

                let make_16 = |addr: u32, val: u16| {
                    Code::Single(match code_type {
                        ByteType::Once => SingleCode::Once16(make_address(addr), val),
                        ByteType::Write => SingleCode::Write16(make_address(addr), val),
                    })
                };

                match prev {
                    Some((paddr, pval)) if paddr + 1 == addr => {
                        result.push(make_16(paddr, (pval as u16) << 8 | (val as u16)));

                        (result, None)
                    }
                    Some((paddr, pval)) => {
                        result.push(make_8(paddr, pval));

                        let prev = if addr & 1 == 0 && i + 1 != count {
                            Some((addr, val))
                        } else {
                            result.push(make_8(addr, val));

                            None
                        };

                        (result, prev)
                    }
                    None if i + 1 == count => {
                        result.push(make_8(addr, val));

                        (result, None)
                    }
                    None if addr & 1 != 0 => {
                        result.push(make_8(addr, val));

                        (result, None)
                    }
                    None => (result, Some((addr, val))),
                }
            },
        )
        .0;

    final_code.extend_from_slice(&ignored);

    ExpandedCode(final_code)
}

pub fn expand_and_sort(code: &[Code]) -> ExpandedCode {
    let mut result = expand_code(code).0;

    result.sort_by_key(|x| x.affected_address());

    ExpandedCode(result)
}

pub fn line_count(codes: &[Code]) -> usize {
    codes
        .iter()
        .map(|x| if x.is_single() { 1 } else { 2 })
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use Code::*;

    use SingleCode::*;

    #[test]
    fn test_str_interp() {
        assert_eq!(
            from_str("80123456 1234"),
            Ok(vec![Single(Write8(Address([0x12, 0x34, 0x56]), 0x34))])
        );
        assert_eq!(
            from_str("81123456 1234"),
            Ok(vec![Single(Write16(Address([0x12, 0x34, 0x56]), 0x1234))])
        );
        assert_eq!(
            from_str("D0123456 1234"),
            Err(GsStrError::Code(GsCodeError::CompositeEof((
                0xD0123456, 0x1234
            ))))
        );
        assert_eq!(
            from_str("50000420 1234\n81123456 1234"),
            Ok(vec![Composite(CompositeCode::Repeat(
                RepeatCount(NonZeroU8::new(4).unwrap()),
                AddressDelta(NonZeroU8::new(32).unwrap()),
                ValueDelta(4660),
                Write16(Address([18, 52, 86]), 4660)
            ))])
        );
        assert_eq!(
            from_str("D0123456 1234\nD0123456 1234"),
            Err(GsStrError::Code(GsCodeError::CompositeError(
                (0xD0123456, 0x1234),
                (0xD0123456, 0x1234),
                GsSingleError::UnknownCodeType(0xD0)
            )))
        );
    }

    #[test]
    fn test_repeat() {
        assert_eq!(
            from_str("50000420 1234\n81123456 1234").map(|x| expand_code(&x)),
            Ok(ExpandedCode(vec![
                Single(Write16(Address([18, 52, 86]), 4660)),
                Single(Write16(Address([18, 52, 118]), 9320)),
                Single(Write16(Address([18, 52, 150]), 13980)),
                Single(Write16(Address([18, 52, 182]), 18640))
            ]))
        )
    }

    #[test]
    fn test_nth_repetition_negative() {
        assert_eq!(
            Write16(Address([0, 0, 0]), 4096).nth_repetition(
                1,
                AddressDelta(NonZeroU8::new(1).unwrap()),
                ValueDelta(-4096)
            ),
            Write16(Address([0, 0, 1]), 0)
        )
    }

    #[test]
    fn test_expand_skip() {
        assert_eq!(
            expand_and_sort(&[
                Code::Single(SingleCode::Write8(make_address(0), 0)),
                Code::Single(SingleCode::Write8(make_address(2), 0)),
                Code::Single(SingleCode::Write8(make_address(4), 0)),
                Code::Single(SingleCode::Write8(make_address(6), 0)),
            ])
            .0,
            vec![
                Single(Write8(Address([0, 0, 0]), 0)),
                Single(Write8(Address([0, 0, 2]), 0)),
                Single(Write8(Address([0, 0, 4]), 0)),
                Single(Write8(Address([0, 0, 6]), 0))
            ]
        )
    }
}
