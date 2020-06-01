use gspro::table::make_numbered_table;
use gspro::{expand_and_sort, line_count, CodeDisplay};
use std::io;
use std::io::Read;
use std::time::Instant;

fn main() -> io::Result<()> {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer)?;

    let code = gspro::from_str(&buffer).expect("Code error");
    let compressed = gspro::compress_code(&code).expect("Compress error");
    let linear = gspro::compress_code_linear(&code).expect("Linear compress error");

    let (x_new, x_original) = (expand_and_sort(&compressed), expand_and_sort(&code));

    if x_new != x_original {
        panic!(
            "Doesn't expand to original!\nOriginal =\n{}\nNew =\n{}\nCompressed =\n{}",
            x_original.get().fmt(),
            x_new.get().fmt(),
            compressed.fmt(),
        );
    }

    let start = Instant::now();

    eprintln!(
        "From {} lines to {}, {:.2}% of original. Time: {:?}.",
        line_count(&code),
        line_count(&compressed),
        (line_count(&compressed) as f64 / line_count(&code) as f64) * 100.0,
        (Instant::now() - start)
    );

    println!();

    println!(
        "{}",
        make_numbered_table(
            "no.",
            &[
                ("compressed", &compressed),
                ("linear", &linear),
                ("original", &code)
            ]
        )
    );

    Ok(())
}
