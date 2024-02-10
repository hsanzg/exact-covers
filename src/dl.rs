use std::mem::MaybeUninit;

use crate::indices::{ItemIndex, NodeIndex};
use crate::Problem;

/// An item in an [XCC problem](`Problem`).
pub(crate) struct Item<'l, L> {
    /// A unique identifier assigned to this item.
    ///
    /// This field roughly corresponds to the `NAME` member in Knuth's
    /// data structure.
    ///
    /// # Invariant
    ///
    /// This variable is initialized if and only if this item does not represent
    /// the special header node in a horizontal list of a [`Solver`].
    label: MaybeUninit<&'l L>,
    /// Possibly the previous item in a (horizontal) list of active items,
    /// in cyclic order. The contents of this variable are preserved when
    /// the item is removed from such linked list. This property makes it
    /// possible to apply the dancing links technique on a list of active
    /// items.
    ///
    /// This field corresponds to the `LLINK` pointer in Knuth's data structure.
    ///
    /// # Invariant
    ///
    /// If `left == right`, then this item represents the special header node
    /// in an empty horizontal list of a [`Solver`].
    left: ItemIndex,
    /// Possibly the next item in a (horizontal) list of active items,
    /// in cyclic order. The contents of this variable are preserved
    /// when the item is removed from such linked list. (See `self.left`
    /// for details.)
    ///
    /// This field corresponds to the `RLINK` pointer in Knuth's data structure.
    right: ItemIndex,
    /// The node of the first active option that contains this item, if any.
    /// In other words, the first node in the vertical list for this item.
    ///
    /// This field corresponds to the `DLINK` pointer in Knuth's data structure.
    ///
    /// # Invariant
    ///
    /// `first_option` is [`None`] if and only if `last_option` is [`None`].
    first_option: Option<NodeIndex>,
    /// The node of the last active option that contains this item, if any.
    /// In other words, the last node in the vertical list for this item.
    ///
    /// This field corresponds to the `ULINK` pointer in Knuth's data structure.
    last_option: Option<NodeIndex>,
    /// The number of elements in the vertical list for this item.
    ///
    /// # Invariants
    ///
    /// - `len == 0` if and only if `first_option` and `last_option` are [`None`].
    /// - `len == 1` if and only if `first_option == last_option`.
    len: usize,
}

impl<'l, L> Item<'l, L> {
    /// Creates the head for an active list of items.
    fn header(left: ItemIndex, right: ItemIndex) -> Self {
        Self {
            label: MaybeUninit::uninit(),
            left,
            right,
            first_option: None,
            last_option: None,
            len: 0,
        }
    }

    /// Creates an item that points to its predecessor and successor
    /// in a horizontal list, and whose vertical list is empty.
    fn new(label: &'l L, left: ItemIndex, right: ItemIndex) -> Self {
        Self {
            label: MaybeUninit::new(label),
            left,
            right,
            first_option: None,
            last_option: None,
            len: 0,
        }
    }
}

/// The position of the special node in the `items` table of a [`Solver`]
/// that serves as the head of the list of active _primary_ items; Knuth
/// called this the _root_ in the paper "Dancing links", [arXiv:cs/0011047][dl]
/// [cs.DS] (2000).
///
/// The list of active secondary items has its own header node, namely the last
/// element in `items`. Its position thus depends on the number of items in
/// the exact cover problem, so this constant has no secondary counterpart.
///
/// [dl]: https://arxiv.org/pdf/cs/0011047.pdf
pub(crate) const PRIMARY_HEADER: ItemIndex = ItemIndex::new(0);

/// An instance of some [item](`Item`) in an option, represented as
/// an internal node in the toroidal data structures of [`Solver`].
pub(crate) struct Instance<C> {
    /// The item associated with this node.
    ///
    /// This field corresponds to the `TOP` pointer in Knuth's data structure.
    item: ItemIndex,
    /// The previous node in the vertical list for `item`, if any.
    ///
    /// This field corresponds to the `ULINK` pointer in Knuth's data structure,
    /// except that it equals [`None`] instead of `item` when a node belongs
    /// to the first option that contains `item`.
    above: Option<NodeIndex>,
    /// The next node in the vertical list for `item`, if any.
    ///
    /// This field corresponds to the `DLINK` pointer in Knuth's data structure,
    /// except that it equals [`None`] instead of `item` when a node belongs
    /// to the last option that contains `item`.
    below: Option<NodeIndex>,
    /// The color assigned to `item` by this option, if any. Otherwise
    /// the solver implicitly assigns a unique color to this instance
    /// that is incompatible with the colors of any other option,
    /// provided that `item` is secondary.
    ///
    /// This field corresponds to the `COLOR` member in Knuth's data structure.
    ///
    /// # Invariant
    ///
    /// If `item` is a primary item, then this variable is [`None`].
    color: Option<C>,
}

/// A node in the sequential table of a [`Solver`] that either is a separator
/// between the items of two options, or it refers to one of these items.
pub(crate) enum Node<C> {
    /// A spacer node between options.
    Spacer {
        /// The first node in the preceding option, or [`None`] if this is
        /// the spacer that comes before the first option.
        ///
        /// This field is an aid to traversing such option in cyclic order,
        /// from left to right. It corresponds to the `ULINK` pointer in
        /// Knuth's data structure.
        first_in_prev: Option<NodeIndex>,
        /// The last node in the succeeding option, or [`None`] if this is
        /// the spacer that comes after the last option.
        ///
        /// This field is an aid to traversing such option in cyclic order,
        /// from right to left.
        last_in_next: Option<NodeIndex>,
    },
    /// An instance of an item in some option.
    Instance(Instance<C>),
}


pub struct Solver<'i, I, C> {
    ///
    items: Vec<Item<'i, I>>,
    nodes: Vec<Node<C>>,
}

impl<'i, I, C> Solver<'i, I, C> {
    pub fn new(problem: Problem<'i, I, C>) -> Self {
        todo!()
    }
}
