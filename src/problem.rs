use crate::indices::{ItemIndex, RecordIndex};
use std::mem::MaybeUninit;

/// An item in an [exact cover problem](`Problem`).
pub(crate) struct Item<'l, L> {
    /// The data associated with this item.
    ///
    /// This field roughly corresponds to the `NAME` member in Knuth's
    /// data structure.
    ///
    /// # Invariant
    ///
    /// This variable is initialized if and only if this item does not represent
    /// the special header node in a horizontal list of a [`Problem`].
    label: MaybeUninit<&'l L>,
    /// Possibly the previous item in a (horizontal) list of active items,
    /// in cyclic order. The contents of this variable are preserved when
    /// the item is removed from such linked list. This property makes it
    /// possible to apply the dancing links technique on list of active
    /// items.
    ///
    /// This field corresponds to the `LLINK` pointer in Knuth's data structure.
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
    first_option: Option<RecordIndex>,
    /// The node of the last active option that contains this item, if any.
    /// In other words, the last node in the vertical list for this item.
    ///
    /// This field corresponds to the `ULINK` pointer in Knuth's data structure.
    last_option: Option<RecordIndex>,
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

/// The position of the special node in the `items` table of a [`Problem`]
/// that serves as the head of the list of active _primary_ items.
///
/// The list of active secondary items has its own header node, namely the last
/// element in `items`. Its position thus depends on the number of items in
/// the exact cover problem, so this constant has no secondary counterpart.
pub(crate) const PRIMARY_HEADER: ItemIndex = ItemIndex::new(0);

/// An internal node in the toroidal data structure of a [`Problem`];
/// each of these nodes represents one [item](`Item`) of an option.
pub(crate) struct Node<C> {
    /// The item associated with this node.
    ///
    /// This field corresponds to the `TOP` pointer in Knuth's data structure.
    item: ItemIndex,
    /// The previous node in the vertical list for `item`, if any.
    ///
    /// This field corresponds to the `ULINK` pointer in Knuth's data structure,
    /// except that it equals [`None`] instead of `item` when a node belongs
    /// to the first option that contains `item`.
    above: Option<RecordIndex>,
    /// The next node in the vertical list for `item`, if any.
    ///
    /// This field corresponds to the `DLINK` pointer in Knuth's data structure,
    /// except that it equals [`None`] instead of `item` when a node belongs
    /// to the last option that contains `item`.
    below: Option<RecordIndex>,
    /// The color assigned to `item` of this option, if any.
    ///
    /// todo: document only valid if this is a secondary item.
    /// todo: note that if no color assigned then the solver behaves as if
    ///       a unique color has been assigned to this item in the option.
    color: Option<C>,
}

pub(crate) enum Record {
    Spacer,
    Node,
}

///
///
/// See the [crate-level documentation](`crate`) for details.
pub(crate) struct Problem<'i, L, C> {
    items: Vec<Item<'i, L>>,
}
