#[macro_use]
mod macros;
mod compress;
mod gs;
pub mod table;

pub use compress::{linear::compress_code_linear, permute::compress_code};
pub use gs::*;
