#[macro_export]
macro_rules! map {
    ($($x:expr => $y:expr),*) => {{
        #[allow(unused_mut)]
        let mut temp_map = std::collections::BTreeMap::new();
        $(temp_map.insert($x, $y);)*
        temp_map
    }}
}

#[macro_export]
macro_rules! set {
    ($($x:expr),*) => {{
        #[allow(unused_mut)]
        let mut temp_set = std::collections::BTreeSet::new();
        $(temp_set.insert($x);)*
        temp_set
    }}
}

