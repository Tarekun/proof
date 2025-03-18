/// Tag union type with a left and a right constructor
/// how rust doesnt natively have this is beyond me
#[derive(Debug, PartialEq, Clone)]
pub enum Union<L, R> {
    L(L),
    R(R),
}

// im like fr?
pub fn simple_map<T, R>(vector: Vec<T>, iterator: impl Fn(T) -> R) -> Vec<R> {
    vector.into_iter().map(iterator).collect()
}

pub fn simple_map_indexed<T, R>(
    vector: Vec<T>,
    iterator: impl Fn((usize, T)) -> R,
) -> Vec<R> {
    vector.into_iter().enumerate().map(iterator).collect()
}
