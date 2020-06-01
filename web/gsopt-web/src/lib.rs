mod utils;

use wasm_bindgen::prelude::*;

// When the `wee_alloc` feature is enabled, use `wee_alloc` as the global
// allocator.
#[cfg(feature = "wee_alloc")]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

use gspro::table::make_numbered_table;
use gspro::*;

#[wasm_bindgen]
pub struct CrushResult {
    compressed: String,
    details: String,
}

#[wasm_bindgen]
impl CrushResult {
    pub fn get_compressed(&self) -> String {
        self.compressed.clone()
    }
    pub fn get_details(&self) -> String {
        self.details.clone()
    }
}

#[wasm_bindgen]
pub fn crush_code(input: &str) -> CrushResult {
    let r = from_str(input)
        .map_err(|e| format!("{:?}", e))
        .and_then(|c| {
            compress_code(&c)
                .map(|x| (c, x))
                .map_err(|e| format!("{:?}", e))
        })
        .map(|(c, x)| CrushResult {
            compressed: x.fmt().to_string(),
            details: make_numbered_table("no.", &[("compressed", &x), ("original", &c)])
                .to_string(),
        });

    (match r {
        Ok(x) => x,
        Err(x) => CrushResult {
            compressed: String::new(),
            details: x,
        },
    })
    .into()
}
