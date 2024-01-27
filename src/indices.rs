use std::fmt::Debug;
use std::num::NonZeroUsize;

/// The position of an item node in a sequential table.
///
/// See the `items` arena in the [`ExactCovers`] struct for an example of
/// this construction.
///
/// [`ExactCovers`]: `crate::xc::ExactCovers`
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[repr(transparent)]
pub(crate) struct ItemIndex(usize);

impl ItemIndex {
    /// Creates a new index.
    pub const fn new(ix: usize) -> Self {
        Self(ix)
    }

    /// Returns the index value as a primitive type.
    pub const fn get(self) -> usize {
        self.0
    }

    /// Returns the position of the previous item in the table.
    ///
    /// The result is meaningful only if `self` is positive.
    pub fn decrement(self) -> Self {
        Self(self.0 - 1)
    }

    /// Returns the position of the next record in the table, if any.
    pub fn increment(self) -> Self {
        Self(self.0 + 1)
    }
}

/// The position of a node in a sequential table, whose first node cannot
/// be referenced. See the `nodes` arena in the [`ExactCovers`] struct for
/// an example of this construction.
///
/// The restriction to positive index values may seem awkward, but it is
/// the only way to exploit the memory layout advantages of [`NonZeroUsize`]
/// while letting [`NodeIndex::get`] be a simple getter that performs no
/// conversion through e.g. bitwise complementation. This additional
/// computation appears in roughly 3% of `perf` samples when running
/// various benchmarks problems. Fortunately, exact cover solvers rarely
/// if ever need to access the first node by index, because it is a spacer
/// (see [`ExactCovers`] for details).
///
/// [`ExactCovers`]: `crate::xc::ExactCovers`
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[repr(transparent)]
pub(crate) struct NodeIndex(NonZeroUsize);

impl NodeIndex {
    /// Creates a new index.
    pub const fn new(ix: usize) -> Self {
        // Workaround for `Option::expect` not being `const fn` in stable Rust.
        Self(if let Some(ix) = NonZeroUsize::new(ix) {
            ix
        } else {
            panic!("node index must be positive")
        })
    }

    /// Returns the index value as a primitive type.
    pub const fn get(self) -> usize {
        self.0.get()
    }

    /// Returns the position of the previous node in the table, or `None`
    /// if this index refers to the second record in the table (that is,
    /// whenever `self.get() == 1`).
    pub fn decrement(self) -> Option<Self> {
        NonZeroUsize::new(self.0.get() - 1).map(Self)
    }

    /// Returns the position of the next node in the table, if any.
    pub fn increment(self) -> Self {
        // Workaround for `Option::expect` not being `const fn` in stable Rust.
        Self(if let Some(ix) = self.0.checked_add(1) {
            ix
        } else {
            panic!("overflow in NodeIndex::increment")
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

        assert_eq!(NodeIndex::new(1).get(), 1);
        assert_eq!(NodeIndex::new(65).get(), 65);
        assert_eq!(NodeIndex::new(87935).get(), 87935);
    }

    #[test]
    #[should_panic]
    fn out_of_bounds_node_index() {
        NodeIndex::new(0);
    }

    #[test]
    fn index_decrement() {
        assert_eq!(ItemIndex::new(1).decrement(), ItemIndex::new(0));
        assert_eq!(ItemIndex::new(15).decrement(), ItemIndex::new(14));

        assert_eq!(NodeIndex::new(1).decrement(), None);
        assert_eq!(NodeIndex::new(2).decrement(), Some(NodeIndex::new(1)));
        assert_eq!(NodeIndex::new(565).decrement(), Some(NodeIndex::new(564)));
    }

    #[test]
    fn index_increment() {
        assert_eq!(ItemIndex::new(0).increment(), ItemIndex::new(1));
        assert_eq!(ItemIndex::new(1).increment(), ItemIndex::new(2));
        assert_eq!(ItemIndex::new(133).increment(), ItemIndex::new(134));

        assert_eq!(NodeIndex::new(1).increment(), NodeIndex::new(2));
        assert_eq!(NodeIndex::new(2).increment(), NodeIndex::new(3));
        assert_eq!(NodeIndex::new(234).increment(), NodeIndex::new(235));
    }
}
