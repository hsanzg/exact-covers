use std::num::NonZeroUsize;

/// The position of an item node in a sequential table.
///
/// See the `items` arena in the [`dl::Solver`] structure for an example of
/// this construction.
///
/// [`dl::Solver`]: `crate::dl::Solver`
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[repr(transparent)]
pub struct ItemIndex(usize);

impl ItemIndex {
    /// Creates a new index.
    #[must_use]
    pub const fn new(ix: usize) -> Self {
        Self(ix)
    }

    /// Returns the index value as a primitive type.
    #[must_use]
    pub const fn get(self) -> usize {
        self.0
    }

    /// Returns the position of the previous item in the table.
    ///
    /// The result is meaningful only if `self` is positive.
    #[must_use]
    pub fn decrement(self) -> Self {
        Self(self.0 - 1)
    }

    /// Returns the position of the next item in the table, if any.
    ///
    /// The result is meaningful only if `self` is less than [`usize::MAX`].
    #[must_use]
    pub fn increment(self) -> Self {
        Self(self.0 + 1)
    }
}

/// The position of a node in a sequential table.
///
/// See the `nodes` arena in the [`dl::Solver`] structure for an example of
/// this construction.
///
/// [`dl::Solver`]: `crate::dl::Solver`
pub type NodeIndex = usize;

/// The position of an item instance in a sequential table, whose first record
/// with index 0 cannot be referenced. See the `nodes` arena in the [`dl::Solver`]
/// structure for an example of this construction.
///
/// The restriction to positive index values may seem awkward, but it is the
/// only way to exploit the memory layout advantages of [`NonZeroUsize`] while
/// letting [`InstIndex::get`] be a simple getter that performs no conversion
/// through e.g. bitwise complementation. This additional computation appears
/// in roughly 3% of `perf` samples when running various benchmark problems.
/// Fortunately, XCC solvers rarely if ever need to access the zeroth node
/// by index, because it is a spacer (see [`dl::Solver`] for details).
///
/// [`dl::Solver`]: `crate::dl::Solver`
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[repr(transparent)]
pub struct InstIndex(NonZeroUsize);

impl InstIndex {
    /// Creates a new index.
    ///
    /// # Panics
    ///
    /// This function panics if `ix` is zero.
    #[must_use]
    pub const fn new(ix: usize) -> Self {
        // Workaround for `Option::expect` not being `const fn` in stable Rust.
        Self(if let Some(ix) = NonZeroUsize::new(ix) {
            ix
        } else {
            panic!("node index must be positive")
        })
    }

    /// Returns the index value as a primitive type.
    #[must_use]
    pub const fn get(self) -> usize {
        self.0.get()
    }

    /// Returns the position of the previous item instance in the table, or
    /// `None` if this index refers to the second record in the table (that is,
    /// whenever `self.get() == 1`).
    #[must_use]
    pub const fn decrement(self) -> Option<Self> {
        // Workaround for `Option::map` not being `const fn` in stable Rust.
        if let Some(ix) = NonZeroUsize::new(self.0.get() - 1) {
            Some(Self(ix))
        } else {
            None
        }
    }

    /// Returns the position of the next record in the table, if any.
    ///
    /// # Safety
    ///
    /// To avoid overflow, the caller must make sure that the current index is
    /// less than [`usize::MAX`]. This function is not marked `unsafe` because
    /// this condition is almost always true in practice: a node arena can
    /// usually hold at most [`isize::MAX`] elements.
    #[must_use]
    pub const fn increment(self) -> Self {
        Self(unsafe { NonZeroUsize::new_unchecked(self.0.get() + 1) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_get() {
        assert_eq!(ItemIndex::new(0).get(), 0);
        assert_eq!(ItemIndex::new(123).get(), 123);
        assert_eq!(ItemIndex::new(456789).get(), 456789);

        assert_eq!(InstIndex::new(1).get(), 1);
        assert_eq!(InstIndex::new(65).get(), 65);
        assert_eq!(InstIndex::new(87935).get(), 87935);
    }

    #[test]
    #[should_panic]
    fn out_of_bounds_node_index() {
        let _ = InstIndex::new(0);
    }

    #[test]
    fn index_decrement() {
        assert_eq!(ItemIndex::new(1).decrement(), ItemIndex::new(0));
        assert_eq!(ItemIndex::new(15).decrement(), ItemIndex::new(14));

        assert!(InstIndex::new(1).decrement().is_none());
        assert_eq!(InstIndex::new(2).decrement(), Some(InstIndex::new(1)));
        assert_eq!(InstIndex::new(565).decrement(), Some(InstIndex::new(564)));
    }

    #[test]
    fn index_increment() {
        assert_eq!(ItemIndex::new(0).increment(), ItemIndex::new(1));
        assert_eq!(ItemIndex::new(1).increment(), ItemIndex::new(2));
        assert_eq!(ItemIndex::new(133).increment(), ItemIndex::new(134));

        assert_eq!(InstIndex::new(1).increment(), InstIndex::new(2));
        assert_eq!(InstIndex::new(2).increment(), InstIndex::new(3));
        assert_eq!(InstIndex::new(234).increment(), InstIndex::new(235));
    }
}
