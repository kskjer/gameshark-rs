use crate::{expand_code, AddressDelta, Code, RepeatCount, SingleCode, SingleCodeType};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::num::NonZeroU8;

pub mod linear;
pub mod permute;

#[derive(Debug)]
pub enum CompressError {
    RepeatOverflowed(SingleCode, usize),
    AddressDeltaOverflowed(SingleCode, u32),
}

fn prepare_code_for_compression(
    code: &[Code],
) -> (Vec<usize>, BTreeMap<SingleCodeType, Vec<SingleCode>>) {
    let (ignored, mut singles) = expand_code(code).get().iter().enumerate().fold(
        (Vec::new(), Vec::new()),
        |(mut ignored, mut singles), (i, cur)| {
            match cur {
                Code::Single(s) => singles.push(*s),
                _ => ignored.push(i),
            }

            (ignored, singles)
        },
    );

    singles.sort_by_key(|x| x.affected_address());

    let by_type = singles
        .iter()
        .copied()
        .fold(BTreeMap::new(), |mut acc, cur| {
            acc.entry(cur.code_type()).or_insert(Vec::new()).push(cur);

            acc
        });

    (ignored, by_type)
}

fn get_repeat_count(count: usize, code: SingleCode) -> Result<RepeatCount, CompressError> {
    Ok(RepeatCount(
        u8::try_from(count)
            .ok()
            .and_then(|v| NonZeroU8::new(v))
            .ok_or(CompressError::RepeatOverflowed(code, count))?,
    ))
}

fn get_address_delta(delta: u32, code: SingleCode) -> Result<AddressDelta, CompressError> {
    Ok(AddressDelta(
        u8::try_from(delta)
            .ok()
            .and_then(|v| NonZeroU8::new(v))
            .ok_or(CompressError::AddressDeltaOverflowed(code, delta))?,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table::make_numbered_table;
    use crate::{expand_and_sort, from_str, CodeDisplay};
    use std::cmp::max;

    pub fn test_eq(code: &str, result: &str, map: impl Fn(&Vec<Code>) -> Vec<Code>) {
        let code = from_str(code).expect("Parse");
        let compressed = map(&code);

        let (str_og, str_cmp) = (
            expand_and_sort(&code).get().fmt().to_string(),
            expand_and_sort(&compressed).get().fmt().to_string(),
        );

        let lines_og_x = str_og.lines().collect::<Vec<_>>();
        let lines_cmp_x = str_cmp.lines().collect::<Vec<_>>();
        let cmp_str = compressed.fmt().to_string();
        let lines_compressed = cmp_str.lines().collect::<Vec<_>>();
        let lines_expected = result.lines().collect::<Vec<_>>();

        macro_rules! compare {
            ($a:expr, $b:expr) => {
                (
                    "!=",
                    &(0..max($a.len(), $b.len()))
                        .map(|i| match ($a.get(i), $b.get(i)) {
                            (Some(x), Some(y)) if x != y => "y",
                            _ => "",
                        })
                        .collect::<Vec<_>>(),
                )
            };
        }

        println!(
            "{}",
            make_numbered_table(
                "no.",
                &[
                    ("input-x", &lines_og_x),
                    compare!(lines_og_x, lines_cmp_x),
                    ("result-x", &lines_cmp_x),
                    ("result", &lines_compressed[..]),
                    compare!(lines_compressed, lines_expected),
                    ("expected", &lines_expected[..])
                ]
            )
        );

        assert_eq!(compressed.fmt().to_string(), result);
        assert_eq!(str_og, str_cmp);
    }
}
