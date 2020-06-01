use std::fmt::{Display, Error, Formatter};
use std::{cmp, iter};

fn expand_line<T: Display>(set: &[T]) -> Vec<String> {
    set.iter()
        .flat_map(|x| {
            let result = x.to_string().lines().map(String::from).collect::<Vec<_>>();

            if result.len() < 1 {
                vec![String::new()]
            } else {
                result
            }
        })
        .collect()
}

pub struct Table<'a, T>(&'a [(&'a str, &'a [T])]);
pub struct NumberedTable<'a, T>(&'a str, Table<'a, T>);

pub fn make_table<'a, T>(data: &'a [(&str, &[T])]) -> Table<'a, T> {
    Table(data)
}

pub fn make_numbered_table<'a, T>(
    line_col_title: &'a str,
    data: &'a [(&str, &[T])],
) -> NumberedTable<'a, T> {
    NumberedTable(line_col_title, Table(data))
}

impl<'a, T: Display> Display for NumberedTable<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let &NumberedTable(line_col_header, Table(sets)) = self;
        let sets = sets
            .iter()
            .map(|(n, v)| (*n, expand_line(v)))
            .collect::<Vec<_>>();
        let longest_col = sets.iter().map(|x| x.1.len()).max().unwrap_or_default();
        let widest_col = sets
            .iter()
            .map(|x| x.1.iter().map(|x| x.len()).max().unwrap_or_default())
            .max()
            .unwrap_or_default();
        let line_nos = (0..longest_col)
            .map(|x| {
                format!(
                    "{:>pad$}",
                    x,
                    pad = cmp::max(widest_col.to_string().len(), line_col_header.len()) + 1
                )
            })
            .collect::<Vec<_>>();

        let to_print = iter::once((line_col_header, &line_nos[..]))
            .chain(sets.iter().map(|(n, v)| (*n, &v[..])))
            .collect::<Vec<_>>();

        Table(&to_print).fmt(f)
    }
}

impl<'a, T: Display> Display for Table<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let data = self.0;
        let col_data = data
            .iter()
            .map(|(_, set)| expand_line(*set))
            .collect::<Vec<_>>();
        let col_lengths = col_data.iter().map(|x| x.len()).collect::<Vec<_>>();
        let col_widths = col_data
            .iter()
            .enumerate()
            .map(|(i, x)| {
                cmp::max(
                    data[i].0.len(),
                    x.iter().map(|x| x.len()).max().unwrap_or_default(),
                )
            })
            .collect::<Vec<_>>();

        let print_col = |f: &mut Formatter,
                         set: Vec<String>,
                         sep: &dyn Fn(usize) -> char|
         -> Result<(), Error> {
            for (i, c) in set.iter().enumerate() {
                write!(f, "{: <pad$}", c, pad = col_widths[i])?;

                if i + 1 != set.len() {
                    write!(f, "  {}  ", sep(i))?;
                }
            }

            writeln!(f)
        };

        print_col(f, data.iter().map(|x| x.0.into()).collect(), &|_| '|')?;
        writeln!(
            f,
            "{:-<pad$}",
            "",
            pad = col_widths.iter().copied().map(|x| x + 5).sum::<usize>() - 5
        )?;

        for r in 0..col_lengths.iter().copied().max().unwrap_or_default() {
            print_col(
                f,
                (0..data.len())
                    .map(|c| col_data[c].get(r).cloned().unwrap_or_default())
                    .collect(),
                &|n| {
                    if n == 0 && col_lengths.iter().any(|&y| y == r) {
                        '^'
                    } else {
                        '|'
                    }
                },
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::table::{NumberedTable, Table};

    #[test]
    fn test_table() {
        assert_eq!(
            "test A  |  test BBB\n-------------------\n1       |  1       \n2       |  2       \n3       |  3       \n        ^  4       \n        |  5       \n",
            Table(&[("test A", &[1, 2, 3]), ("test BBB", &[1, 2, 3, 4, 5])]).to_string()
        );
    }

    #[test]
    fn test_table_numbered() {
        assert_eq!(
            "no.   |  test A  |  test BBB\n----------------------------\n   0  |  1       |  1       \n   1  |  2       |  2       \n   2  |  3       |  3       \n   3  ^          |  4       \n   4  |          |  5       \n",
            NumberedTable("no.", Table(&[("test A", &[1, 2, 3]), ("test BBB", &[1, 2, 3, 4, 5])])).to_string()
        );
    }
}
