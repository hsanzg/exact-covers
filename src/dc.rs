use crate::indices::InstIndex;
use crate::Solution;

/// Visits all solutions to a given XCC problem by means of dancing cells.
///
/// More precisely, this structure embodies an implementation of Algorithm C,
/// as presented by D. E. Knuth in Section 7.2.2.3 of [_TAOCP_ **4C** (June 25, 2024)][taocp4c],
/// Pre-Fascicle 7A (preliminary draft), pages 63–64.
///
/// [taocp4c]: https://cs.stanford.edu/~knuth/fasc7a.ps.gz
pub struct Solver;

impl<'i, I: Eq, C: Eq + Copy> crate::Solver<'i, I, C> for Solver {
    fn new(primary: &'i [I], secondary: &'i [I]) -> Self {
        todo!()
    }

    fn add_option<P, S>(&mut self, primary: P, secondary: S)
    where
        P: AsRef<[I]>,
        S: AsRef<[(I, Option<C>)]>,
    {
        todo!()
    }

    fn solve<F>(self, visit: F)
    where
        F: FnMut(Solution<'_, 'i, I, C, Self>),
    {
        todo!()
    }
}

impl<'i, I: Eq, C: Eq + Copy> crate::private::Solver<'i, I, C> for Solver {
    fn pointer(&self, level: usize) -> Option<InstIndex> {
        todo!()
    }

    fn level(&self) -> usize {
        todo!()
    }

    fn option_of(&self, ix: InstIndex, result: &mut Vec<&'i I>) {
        todo!()
    }
}
