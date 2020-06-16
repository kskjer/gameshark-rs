use crate::compress::{
    get_address_delta, get_repeat_count, prepare_code_for_compression, CompressError,
};
use crate::{
    line_count, make_address, Code, CompositeCode, SingleCode, SingleCodeType, ValueDelta,
};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{RangeInclusive, Sub};

#[derive(Debug, PartialEq, Clone)]
struct DualSeries<T> {
    da: T,
    dv: T,
    path: Vec<usize>,
}

fn get_contiguous_groups<T, S>(
    code: &[T],
    step: S,
    v: impl Fn(&T) -> S,
) -> Vec<RangeInclusive<usize>>
where
    S: PartialEq + Sub<Output = S>,
{
    code.iter()
        .enumerate()
        .skip(1)
        .fold(
            (Vec::new(), 0, 0),
            |(mut result, good_start, last_good), (i, cur_code)| {
                if v(cur_code) - v(&code[last_good]) != step {
                    result.push(good_start..=last_good);

                    if i + 1 == code.len() {
                        result.push(i..=i);
                    }

                    (result, i, i)
                } else {
                    if i + 1 == code.len() {
                        result.push(good_start..=i);
                    }

                    (result, good_start, i)
                }
            },
        )
        .0
}

fn mode<T>(code: impl IntoIterator<Item = T>) -> Option<(T, usize)>
where
    T: PartialOrd + Ord + Copy,
{
    let mut set = BTreeMap::new();

    for c in code {
        *set.entry(c).or_insert(0) += 1;
    }

    set.into_iter().max_by_key(|(_val, count)| *count)
}

fn find_series_for_addr_and_val(
    total: usize,
    val_delta_mask: u32,
    addr: &impl Fn(usize) -> u32,
    val: &impl Fn(usize) -> u32,
) -> Vec<DualSeries<i32>> {
    let mut reserved = BTreeSet::new();
    let mut result = Vec::new();

    'outer: for i in 0..total {
        let (ba, bv) = (addr(i), val(i));

        for j in (i + 1)..total {
            let (ca, cv) = (addr(j), val(j));
            let (da, dv) = (ca.wrapping_sub(ba), cv.wrapping_sub(bv));
            let (mut na, mut nv) = (ca.wrapping_add(da), cv.wrapping_add(dv) & val_delta_mask);
            let mut path = vec![i, j];

            if da > 255 {
                continue 'outer;
            }

            for k in (j + 1)..total {
                if reserved.contains(&(da, dv, k)) {
                    continue;
                }

                /*
                println!("      {} / {}", i, j);
                println!("@{:<4} {:?}", k, ((ba, bv), "=>", (ca, cv), "=>", (na, nv), "==", (addr(k), val(k))));
                println!("      da = {}, dv = {}, path = {:?}", da, dv as i32, path);
                println!();
                */

                if na == addr(k) && nv == val(k) {
                    na = na.wrapping_add(da);
                    nv = nv.wrapping_add(dv) & val_delta_mask;
                    path.push(k);
                } else if addr(k) > na {
                    break;
                }
            }

            if path.len() >= 3 {
                for &p in &path {
                    reserved.insert((da, dv, p));
                }

                result.push(DualSeries {
                    da: da as i32,
                    dv: dv as i32,
                    path,
                });
            }
        }
    }

    result
}

fn get_valid_subgroups(groups: Vec<DualSeries<i32>>, taken: &[bool]) -> Vec<DualSeries<i32>> {
    groups
        .into_iter()
        .flat_map(|c| {
            if c.path.iter().any(|n| taken[*n]) {
                c.path
                    .split(|n| taken[*n])
                    .filter(|c| c.len() >= 3)
                    .map(|x| DualSeries {
                        path: x.to_vec(),
                        ..c
                    })
                    .collect::<Vec<_>>()
            } else {
                vec![c]
            }
        })
        .collect()
}

fn compress_iter(
    code: &[SingleCode],
    mut partial: Vec<Code>,
    mut series: Vec<DualSeries<i32>>,
    mut taken: Vec<bool>,
) -> Result<Vec<Vec<Code>>, CompressError> {
    let mut results = Vec::new();

    while let Some(cur) = series.pop() {
        //println!("--> {:?}", cur);

        let start_code = code[cur.path[0]];

        partial.push(Code::Composite(CompositeCode::Repeat(
            get_repeat_count(cur.path.len(), start_code)?,
            get_address_delta(cur.da as u32, start_code)?,
            ValueDelta(cur.dv as i16),
            start_code,
        )));

        for x in cur.path {
            taken[x] = true;
        }

        series = get_valid_subgroups(series, &taken);
        series.sort_by_key(|x| x.path.len());

        //println!("<== {:?}", series);

        let next = series.last();
        let permute_candidates = next
            .into_iter()
            .flat_map(|x| {
                (0..series.len())
                    .rev()
                    .skip(1)
                    .take_while(|&y| series[y].path.len() == x.path.len())
                    .filter(|&y| series[y].path.iter().any(|a| x.path.contains(a)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        if permute_candidates.len() <= 1 {
            continue;
        }

        for i in permute_candidates {
            let mut cloned = series.clone();
            cloned.swap(series.len() - 1, i);

            results.extend_from_slice(&compress_iter(
                code,
                partial.clone(),
                cloned,
                taken.clone(),
            )?);
        }

        break;
    }

    for (i, t) in taken.into_iter().enumerate() {
        if !t {
            partial.push(Code::Single(code[i]));
        }
    }

    //println!("++> {}\n{}", crate::line_count(&partial), crate::PrintCode(&partial));

    results.push(partial);

    Ok(results)
}

fn compress_code_of_type(
    code_type: SingleCodeType,
    code: &[SingleCode],
) -> Result<Vec<Code>, CompressError> {
    let default = compress_code_of_type_inner(code_type, code)?;

    if code_type != SingleCodeType::Write16 {
        return Ok(default);
    }

    let groups = get_contiguous_groups(code, 2, |x| x.affected_address());

    test_trace!("Groups for type {:?} = {:#04X?}", code_type, groups);
    //test_trace!("Raw form = {:#04X?}", code);

    // Find the mode of the values in contiguous regions, and fill the region with that value before
    // applying other codes. This can lead to some savings.
    let base_fill_repeaters = groups
        .iter()
        .map(|x| {
            Ok(match mode(code[x.clone()].iter().map(|x| x.rhs())) {
                Some((mode, count)) if count >= 3 && count <= 255 => {
                    let base_code = code[*x.start()];
                    let repeater = Code::Composite(CompositeCode::Repeat(
                        get_repeat_count(x.clone().count(), base_code)?,
                        get_address_delta(2, base_code)?,
                        ValueDelta(0),
                        SingleCode::Write16(make_address(base_code.affected_address()), mode),
                    ));

                    Some((mode, x.clone(), repeater))
                }
                Some(_) | None => None,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    test_trace!("Base repeaters = {:#04X?}", base_fill_repeaters);

    let (repeaters, other) = base_fill_repeaters.into_iter().enumerate().fold(
        (Vec::new(), Vec::new()),
        |(mut repeaters, mut other), (i, cur)| {
            match cur {
                Some((mode, range, repeater)) => {
                    repeaters.push(repeater);
                    other.extend(code[range].iter().copied().filter(|x| x.rhs() != mode));
                }
                None => {
                    other.extend_from_slice(&code[groups[i].clone()]);
                }
            }

            (repeaters, other)
        },
    );

    test_trace!("Repeaters = {:#04X?}", repeaters);
    test_trace!("Other = {:#04X?}", other);

    let other_code = compress_code_of_type_inner(code_type, &other).map(|x| {
        let mut tmp = repeaters.to_vec();

        tmp.extend(&x);

        test_trace!(
            "Base repeater code (len {} vs default {}):\n{}",
            tmp.len(),
            default.len(),
            crate::table::make_numbered_table("no.", &[("repeater", &tmp), ("default", &default),])
        );

        tmp
    })?;

    Ok(vec![other_code, default]
        .into_iter()
        .min_by_key(|x| x.len())
        .unwrap())
}

fn compress_code_of_type_inner(
    code_type: SingleCodeType,
    code: &[SingleCode],
) -> Result<Vec<Code>, CompressError> {
    let mut series = find_series_for_addr_and_val(
        code.len(),
        code_type.value_mask().into(),
        &|v| code[v].affected_address(),
        &|v| code[v].rhs().into(),
    );

    series.sort_by_key(|x| x.path.len());

    let largest_group = series.last().map(|x| x.path.len());
    let next_largest_group = largest_group
        .and_then(|x| series.iter().rev().skip_while(|y| y.path.len() == x).nth(0))
        .map(|x| x.path.len());

    let mut result = series
        .iter()
        .enumerate()
        .rev()
        .take_while(|(_, x)| x.path.len() >= next_largest_group.unwrap_or_default())
        .map(|(i, _)| {
            //println!("trying @ {:?}", series[i]);

            compress_iter(
                &code,
                Vec::new(),
                {
                    let mut clone = series.clone();
                    clone.swap(series.len() - 1, i);

                    clone
                },
                vec![false; code.len()],
            )
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flat_map(|x| x)
        .min_by_key(|x| line_count(&x))
        .unwrap_or_default();

    if series.len() == 0 {
        result.extend(code.iter().copied().map(Code::Single));
    }

    Ok(result)
}

pub fn compress_code(code: &[Code]) -> Result<Vec<Code>, CompressError> {
    let (ignored, by_type) = prepare_code_for_compression(code);
    let mut result = Vec::new();

    for (code_type, code) in by_type {
        let for_type = compress_code_of_type(code_type, &code)
            .into_iter()
            .min_by_key(|x| line_count(&x))
            .expect("Result set shouldn't be empty");

        result.extend_from_slice(&for_type);
    }

    result.extend(&ignored);
    result.sort_by_key(|x| x.affected_address());

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compress::tests::test_eq;
    use std::cmp::Reverse;

    fn permute_compress_eq(code: &str, result: &str) {
        test_eq(code, result, |c| compress_code(c).expect("Compress"));
    }

    #[test]
    fn test_address_and_value_series() {
        let pairs = (0u32..16)
            .map(|i| (i, if i < 8 { i } else { i * 7 }))
            .collect::<Vec<_>>();
        let mut results =
            find_series_for_addr_and_val(pairs.len(), 0xFFFF, &|v| pairs[v].0, &|v| pairs[v].1);

        results.sort_by_key(|c| Reverse(c.path.len()));

        assert_eq!(
            results.into_iter().take(2).collect::<Vec<_>>(),
            vec![
                DualSeries {
                    da: 1,
                    dv: 1,
                    path: vec![0, 1, 2, 3, 4, 5, 6, 7]
                },
                DualSeries {
                    da: 1,
                    dv: 7,
                    path: vec![8, 9, 10, 11, 12, 13, 14, 15]
                }
            ]
        )
    }

    #[test]
    fn test_contiguous_groups() {
        assert_eq!(
            vec![0..=4, 5..=5],
            get_contiguous_groups(&[0, 2, 4, 6, 8, 12], 2, |v| *v)
        )
    }

    #[test]
    fn test_contiguous_groups_tail() {
        assert_eq!(
            vec![0..=4, 5..=6],
            get_contiguous_groups(&[0, 2, 4, 6, 8, 12, 14], 2, |v| *v)
        )
    }

    #[test]
    fn test_contiguous_groups_ben() {
        assert_eq!(
            vec![0..=0, 1..=1, 2..=3],
            get_contiguous_groups(
                &[0x81117DEAu32, 0x81117DEE, 0x81500000, 0x81500002,],
                2,
                |v| *v
            )
        )
    }

    #[test]
    fn test_mode() {
        assert_eq!(Some((8, 4)), mode(vec![8, 8, 8, 8, 4, 4, 2, 2, 3, 3, 3]))
    }

    #[test]
    fn test_valid_subgroups() {
        let taken = vec![false, false, false, true, false, false, false];
        let parts = vec![DualSeries {
            da: 1,
            dv: 1,
            path: vec![0, 1, 2, 3, 4, 5, 6],
        }];

        assert_eq!(
            get_valid_subgroups(parts, &taken),
            vec![
                DualSeries {
                    da: 1,
                    dv: 1,
                    path: vec![0, 1, 2]
                },
                DualSeries {
                    da: 1,
                    dv: 1,
                    path: vec![4, 5, 6]
                }
            ]
        );
    }

    #[test]
    fn test_permute_compress() {
        permute_compress_eq(
            "80000002 0000
            80000003 0000
            80000005 0000
            80000007 0000
            8000000B 0000
            8000000D 0000
            80000013 0000
            80000014 0000
            80000016 0000
            80000018 0000
            8000001C 0000
            8000001E 0000
            80000024 0000
            80000025 0000
            80000027 0000
            80000029 0000
            8000002D 0000
            8000002F 0000",
            "81000002 0000\n50000311 0000\n80000005 0000\n50000311 0000\n80000007 0000\n50000311 0000\n8000000B 0000\n50000311 0000\n8000000D 0000\n80000013 0000\n80000014 0000\n81000024 0000\n",
        );
    }

    #[test]
    fn test_permute_values() {
        permute_compress_eq(
            "81000000 0000
            81000002 0000
            81000004 0000
            81000006 ABCD
            81000008 0000
            8100000A 0000
            8100000C 0000",
            "50000702 0000\n81000000 0000\n81000006 ABCD\n",
        )
    }

    #[test]
    fn test_permute_values_inc() {
        permute_compress_eq(
            "81000000 0001
            81000002 0002
            81000004 0003
            81000006 ABCD
            81000008 0004
            8100000A 0005
            8100000C 0006",
            "50000302 0001\n81000000 0001\n81000006 ABCD\n50000302 0001\n81000008 0004\n",
        )
    }

    #[test]
    fn test_permute_with_mixed_type() {
        permute_compress_eq(
            "81000000 0001
            81000002 0002
            81000004 0003
            80000006 00CD",
            "50000302 0001\n81000000 0001\n80000006 00CD\n",
        )
    }

    #[test]
    fn test_permute_ben() {
        permute_compress_eq(
            "D10C5480 AFB0
            810A62A4 0C14
            D10C5480 AFB0
            810A62A6 0000
            81117DEA 062A
            81117DEE 0838
            81500000 2404
            81500002 0853
            81500004 1464
            81500006 000A
            81500008 0000
            8150000A 0000
            8150000C 2404
            8150000E 0010
            81500010 1144
            81500012 0004
            81500014 0000
            81500016 0000
            81500018 2404
            8150001A 062A
            8150001C 1000
            8150001E 0017
            81500020 0000
            81500022 0000
            81500024 2404
            81500026 0838
            81500028 1000
            8150002A 0014
            8150002C 0000
            8150002E 0000
            81500030 2404
            81500032 0855
            81500034 1464
            81500036 0004
            81500038 0000
            8150003A 0000
            8150003C 2404
            8150003E 061C
            81500040 1000
            81500042 000E
            81500044 0000
            81500046 0000
            81500048 2404
            8150004A 080A
            8150004C 1464
            8150004E 0004
            81500050 0000
            81500052 0000
            81500054 2404
            81500056 060E
            81500058 1000
            8150005A 0008
            8150005C 0000
            8150005E 0000
            81500060 2404
            81500062 062E
            81500064 1464
            81500066 0004
            81500068 0000
            8150006A 0000
            8150006C 2404
            8150006E 083A
            81500070 1000
            81500072 0002
            81500074 0000
            81500076 0000
            81500078 0040
            8150007A 2025
            8150007C 0803
            8150007E 59D3
            81500080 0000
            81500082 0000",
            "D10C5480 AFB0
810A62A4 0C14
D10C5480 AFB0
810A62A6 0000
81117DEA 062A
81117DEE 0838
50004202 0000
81500000 0000
50000A0C 0000
81500000 2404
81500002 0853
81500004 1464
81500006 000A
8150000E 0010
81500010 1144
81500012 0004
8150001A 062A
8150001C 1000
8150001E 0017
81500026 0838
50000418 0000
81500028 1000
50000418 FFFA
8150002A 0014
81500032 0855
50000318 0000
81500034 1464
50000318 0000
81500036 0004
8150003E 061C
8150004A 080A
81500056 060E
81500062 062E
8150006E 083A
81500078 0040
8150007A 2025
8150007C 0803
8150007E 59D3\n",
        )
    }
}
