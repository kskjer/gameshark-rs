use crate::compress::{
    get_address_delta, get_repeat_count, prepare_code_for_compression, CompressError,
};
use crate::{line_count, Code, CompositeCode, SingleCode, SingleCodeType, ValueDelta};
use std::collections::BTreeSet;

#[derive(Debug, PartialEq, Clone)]
struct DualSeries<T> {
    da: T,
    dv: T,
    path: Vec<usize>,
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
    code: Vec<SingleCode>,
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
        result.extend_from_slice(&code.into_iter().map(Code::Single).collect::<Vec<_>>());
    }

    Ok(result)
}

pub fn compress_code(code: &[Code]) -> Result<Vec<Code>, CompressError> {
    let (ignored, by_type) = prepare_code_for_compression(code);
    let mut result = Vec::new();

    for (code_type, code) in by_type {
        let for_type = compress_code_of_type(code_type, code)
            .into_iter()
            .min_by_key(|x| line_count(&x))
            .expect("Result set shouldn't be empty");

        result.extend_from_slice(&for_type);
    }

    for i in ignored {
        result.push(code[i]);
    }

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
            "50000311 0000\n80000002 0000\n50000304 0000\n80000003 0000\n50000311 0000\n80000005 0000\n50000311 0000\n8000000D 0000\n50000304 0000\n80000014 0000\n50000304 0000\n80000025 0000\n",
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
            "50000404 0000\n81000000 0000\n81000002 0000\n81000006 ABCD\n8100000A 0000\n",
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
}
