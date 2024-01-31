use std::num::NonZeroUsize;

/// The position of an item node in a sequential table.
///
/// See the `items` arena in the [`Problem`] structure for an example of
/// this construction.
///
/// [`Problem`]: `crate::Problem`
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[repr(transparent)]
pub(crate) struct ItemIndex(usize);

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
    #[must_use]
    pub fn increment(self) -> Self {
        Self(self.0 + 1)
    }
}

/// The position of a record in a sequential table, whose first element cannot
/// be referenced. See the `records` arena in the [`Problem`] structure for
/// an example of this construction.
///
/// The restriction to positive index values may seem awkward, but it is
/// the only way to exploit the memory layout advantages of [`NonZeroUsize`]
/// while letting [`RecordIndex::get`] be a simple getter that performs
/// no conversion through e.g. bitwise complementation. This additional
/// computation appears in roughly 3% of `perf` samples when running
/// various benchmark problems. Fortunately, [`Solver`] rarely needs
/// to access the first record by index, because it is a [spacer].
///
/// [`Problem`]: `crate::Problem`
/// [`Solver`]: `crate::Solver`
/// [spacer]: `crate::problem::Record::Spacer`
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[repr(transparent)]
pub(crate) struct RecordIndex(NonZeroUsize);

impl RecordIndex {
    /// Creates a new index.
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

    /// Returns the position of the previous record in the table, or [`None`]
    /// if the result would refer to the first [spacer] (that is, whenever
    /// `self.get() == 1`).
    ///
    /// [spacer]: `crate::problem::Record::Spacer`
    #[must_use]
    pub fn decrement(self) -> Option<Self> {
        NonZeroUsize::new(self.0.get() - 1).map(Self)
    }

    /// Returns the position of the next record in the table, if any.
    #[must_use]
    pub fn increment(self) -> Self {
        // Workaround for `Option::expect` not being `const fn` in stable Rust.
        Self(if let Some(ix) = self.0.checked_add(1) {
            ix
        } else {
            panic!("overflow in RecordIndex::increment")
        })
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

        assert_eq!(RecordIndex::new(1).get(), 1);
        assert_eq!(RecordIndex::new(65).get(), 65);
        assert_eq!(RecordIndex::new(87935).get(), 87935);
    }

    #[test]
    #[should_panic]
    fn out_of_bounds_node_index() {
        RecordIndex::new(0);
    }

    #[test]
    fn index_decrement() {
        assert_eq!(ItemIndex::new(1).decrement(), ItemIndex::new(0));
        assert_eq!(ItemIndex::new(15).decrement(), ItemIndex::new(14));

        assert!(RecordIndex::new(1).decrement().is_none());
        assert_eq!(RecordIndex::new(2).decrement(), Some(RecordIndex::new(1)));
        assert_eq!(
            RecordIndex::new(565).decrement(),
            Some(RecordIndex::new(564))
        );
    }

    #[test]
    fn index_increment() {
        assert_eq!(ItemIndex::new(0).increment(), ItemIndex::new(1));
        assert_eq!(ItemIndex::new(1).increment(), ItemIndex::new(2));
        assert_eq!(ItemIndex::new(133).increment(), ItemIndex::new(134));

        assert_eq!(RecordIndex::new(1).increment(), RecordIndex::new(2));
        assert_eq!(RecordIndex::new(2).increment(), RecordIndex::new(3));
        assert_eq!(RecordIndex::new(234).increment(), RecordIndex::new(235));
    }
}
