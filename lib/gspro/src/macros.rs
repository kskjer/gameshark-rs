macro_rules! test_trace {
    ($($x:tt)*) => {
        #[cfg(test)]
        println!($($x)*)
    };
}
