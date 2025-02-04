/// Tag union type with a left and a right constructor
/// how rust doesnt natively have this is beyond me
#[derive(Debug, PartialEq)] //support toString printing and equality check
pub enum Union<L, R> {
    L(L),
    R(R),
}
