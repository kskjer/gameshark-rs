use crate::compress::{
    get_address_delta, get_repeat_count, prepare_code_for_compression, CompressError,
};
use crate::{Code, CompositeCode, SingleCode, SingleCodeType, ValueDelta};

fn compress_code_of_type_linear(
    code_type: SingleCodeType,
    original_code: &[SingleCode],
    result: &mut Vec<Code>,
) -> Result<Vec<bool>, CompressError> {
    let value_mask = code_type.value_mask();
    let code = original_code
        .iter()
        .map(|c| (c.affected_address(), c.rhs()))
        .collect::<Vec<_>>();
    let mut taken = vec![false; code.len()];
    let mut resume_at = 0;

    if original_code.len() < 3 {
        return Ok(taken);
    }

    'outer: for i in 0..(code.len() - 2) {
        if i < resume_at {
            continue;
        }

        let (ba, bv) = code[i];

        for j in (i + 1)..(code.len() - 1) {
            let (na, nv) = code[j];
            let (da, dv) = (na.wrapping_sub(ba), nv.wrapping_sub(bv));

            if da > 255 {
                break;
            }

            for k in (j + 1)..code.len() {
                let occurrence = k - i;
                let expected = (
                    ba.wrapping_add(da.wrapping_mul(occurrence as u32)),
                    bv.wrapping_add((dv as u32 * occurrence as u32) as u16) & value_mask,
                );

                //println!("{:X?}", (i, j, k, occurrence, (da, dv), expected, code[k]));

                match (expected != code[k], occurrence > 2, k + 1 != code.len()) {
                    (true, false, _) | (false, false, false) => continue 'outer,
                    (false, _, true) => continue,
                    // Valid repeater code, but invalid cur code or at the end of code list
                    (cur_is_invalid, true, _) => {
                        let count = occurrence + if cur_is_invalid { 0 } else { 1 };

                        for x in 0..count {
                            taken[i + x] = true;
                        }

                        result.push(Code::Composite(CompositeCode::Repeat(
                            get_repeat_count(count, original_code[k])?,
                            get_address_delta(da, original_code[k])?,
                            ValueDelta(dv as i16),
                            original_code[i],
                        )));

                        resume_at = i + count;
                        continue 'outer;
                    }
                }
            }

            break;
        }
    }

    Ok(taken)
}

fn get_not_taken_codes(codes: &[SingleCode], taken: &[bool]) -> Vec<SingleCode> {
    codes
        .iter()
        .copied()
        .enumerate()
        .filter(|(i, _)| !taken[*i])
        .map(|(_, c)| c)
        .collect()
}

pub fn compress_code_linear(code: &[Code]) -> Result<Vec<Code>, CompressError> {
    let (ignored, by_type) = prepare_code_for_compression(code);
    let mut result = Vec::new();

    for (code_type, mut original_code) in by_type {
        let mut last_count = result.len();

        let (taken, leftover) = loop {
            let taken = compress_code_of_type_linear(code_type, &original_code, &mut result)?;
            let mut leftover = get_not_taken_codes(&original_code, &taken);

            leftover.sort_by_key(|c| c.rhs());

            let taken = compress_code_of_type_linear(code_type, &leftover, &mut result)?;

            if last_count == result.len() {
                break (taken, leftover);
            }

            original_code = get_not_taken_codes(&leftover, &taken);
            original_code.sort_by_key(|c| c.affected_address());
            last_count = result.len();
        };

        for (i, t) in taken.into_iter().enumerate() {
            if !t {
                result.push(Code::Single(leftover[i]));
            }
        }
    }

    for i in ignored {
        result.push(code[i]);
    }

    result.sort_by_key(|x| x.affected_address());

    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::compress::linear::compress_code_linear;
    use crate::compress::tests::test_eq;

    fn linear_compress_eq(code: &str, result: &str) {
        test_eq(code, result, |c| compress_code_linear(c).expect("Compress"));
    }

    #[test]
    fn test_linear_compress() {
        linear_compress_eq(
            "80000000 0000
                80000002 0000
                80000004 0000
                80000006 0000",
            "50000402 0000\n80000000 0000\n",
        );
    }

    #[test]
    fn test_linear_compress_two() {
        linear_compress_eq(
            "80000000 0000
            80000002 0000
            80000004 0000
            80000006 0000
            80000010 0000
            80000012 0000
            80000014 0000
            80000016 0000",
            "50000402 0000\n80000000 0000\n50000402 0000\n80000010 0000\n",
        );
    }

    #[test]
    fn test_linear_compress_groups() {
        linear_compress_eq(
            "80000000 0000
            80000002 0000
            80000004 0000
            80000006 0000
            A0000001 0000
            A0000003 0000
            A0000005 0000
            A0000007 0000",
            "50000402 0000\n80000000 0000\n50000402 0000\nA0000001 0000\n",
        );
    }

    #[test]
    fn test_linear_compress_stragglers() {
        linear_compress_eq(
            "80000000 00FF
            80000002 0000
            80000004 0000
            80000006 0000
            8000000A 00FF",
            "80000000 00FF\n50000302 0000\n80000002 0000\n8000000A 00FF\n",
        );
    }

    #[test]
    fn test_linear_compress_interspersed() {
        linear_compress_eq(
            "80000000 00FF
            80000002 0000
            80000004 0000
            80000006 0000
            8000000A 00FF
            80000010 00FF
            80000012 0000
            80000014 0000
            80000016 0000
            8000001A 00FF",
            "80000000 00FF\n50000302 0000\n80000002 0000\n8000000A 00FF\n80000010 00FF\n50000302 0000\n80000012 0000\n8000001A 00FF\n"
        );
    }

    #[test]
    fn test_linear_compress_value() {
        linear_compress_eq(
            "80000000 0001
            80000002 0002
            80000004 0003
            80000006 0004",
            "50000402 0001\n80000000 0001\n",
        );
    }

    #[test]
    fn test_linear_compress_value_neg() {
        linear_compress_eq(
            "80000000 0001
            80000002 0000
            80000004 00FF
            80000006 00FE",
            "50000402 FFFF\n80000000 0001\n",
        );
    }

    #[test]
    fn test_linear_compress_value_neg_16() {
        linear_compress_eq(
            "81000000 0001
            81000002 0000
            81000004 FFFF
            81000006 FFFE",
            "50000402 FFFF\n81000000 0001\n",
        );
    }

    #[test]
    fn test_linear_iterative() {
        linear_compress_eq(
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
            "D10C5480 AFB0\n810A62A4 0C14\nD10C5480 AFB0\n810A62A6 0000\n81117DEA 062A\n81117DEE 0838\n50000A0C 0000\n81500000 2404\n81500002 0853\n81500004 1464\n81500006 000A\n81500008 0000\n8150000A 0000\n8150000E 0010\n81500010 1144\n81500012 0004\n81500014 0000\n81500016 0000\n8150001A 062A\n8150001C 1000\n8150001E 0017\n81500020 0000\n81500022 0000\n81500026 0838\n50000418 0000\n81500028 1000\n8150002A 0014\n8150002C 0000\n8150002E 0000\n81500032 0855\n50000318 0000\n81500034 1464\n50000318 0000\n81500036 0004\n81500038 0000\n8150003A 0000\n8150003E 061C\n81500042 000E\n81500044 0000\n81500046 0000\n8150004A 080A\n81500050 0000\n81500052 0000\n81500056 060E\n8150005A 0008\n8150005C 0000\n8150005E 0000\n81500062 062E\n81500068 0000\n8150006A 0000\n8150006E 083A\n81500072 0002\n81500074 0000\n81500076 0000\n81500078 0040\n8150007A 2025\n8150007C 0803\n8150007E 59D3\n81500080 0000\n81500082 0000\n"
        );
    }

    #[test]
    fn test_linear_luigiblood() {
        linear_compress_eq("
            8014FE0B 0001
            8014FE0F 0001
            8014FE13 0001
            8014FE17 0001
            8014FE1B 0001
            8014FE1F 0001
            8014FE2B 0001
            8014FE2F 0001
            8014FE43 0001
            8014FE47 0001
            8014FE4B 0001
            8014FE4F 0001
            8014FE53 0001
            8014FE57 0001
            8014FE5B 0001
            8014FE63 0001
            8014FE6F 0001
            8014FE73 0001
            8014FE77 0001
            8014FE7B 0001
            8014FE7F 0001
            8014FE83 0001
            8014FE87 0001
            8014FE8B 0001
            8014FE93 0001
            8014FE97 0001
            8014FE9B 0001
            8014FE9F 0001
            8014FEAF 0001
            8014FEB3 0001
            8014FEB7 0001
            8014FEBB 0001
            8014FEBF 0001
            8014FEC3 0001
            8014FEC7 0001",
                           "50000604 0000\n8014FE0B 0001\n8014FE2B 0001\n8014FE2F 0001\n50000704 0000\n8014FE43 0001\n8014FE63 0001\n50000804 0000\n8014FE6F 0001\n50000404 0000\n8014FE93 0001\n50000704 0000\n8014FEAF 0001\n"
        );
    }

    #[test]
    fn test_linear_luigiblood_partial() {
        linear_compress_eq(
            "
            8014FE0B 0001
            8014FE0F 0001
            8014FE13 0001
            8014FE17 0001
            8014FE1B 0001
            8014FE1F 0001",
            "50000604 0000\n8014FE0B 0001\n",
        );
    }
}
