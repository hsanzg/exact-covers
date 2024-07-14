use crate::indices::{InstIndex, ItemIndex, NodeIndex};
use crate::Solution;
use std::iter;
use std::marker::PhantomData;
use std::mem::MaybeUninit;

/// An item in an XCC problem.
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
    first_option: Option<InstIndex>,
    /// The node of the last active option that contains this item, if any.
    /// In other words, the last node in the vertical list for this item.
    ///
    /// This field corresponds to the `ULINK` pointer in Knuth's data structure.
    last_option: Option<InstIndex>,
    /// The number of elements in the vertical list for this item.
    ///
    /// # Invariants
    ///
    /// - `len == 0` if and only if `first_option` and `last_option` are [`None`].
    /// - `len == 1` if and only if `first_option == last_option`.
    len: usize,
    /// Whether this item is secondary and appears in a chosen option that
    /// specifies its color explicitly. This field is true if and only if
    /// $\text{COLOR}(i)\ne0$ in Knuth's Algorithm C, and it helps us to
    /// determine if a solution intersects every purely secondary option
    /// in method [`is_valid_solution`].
    ///
    /// [`is_valid_solution`]: Solver::is_valid_solution
    purified: bool,
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
            purified: false,
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
            purified: false,
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
    above: Option<InstIndex>,
    /// The next node in the vertical list for `item`, if any.
    ///
    /// This field corresponds to the `DLINK` pointer in Knuth's data structure,
    /// except that it equals [`None`] instead of `item` when a node belongs
    /// to the last option that contains `item`.
    below: Option<InstIndex>,
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
    /// If this instance appears in the vertical list of a purified secondary
    /// item, this field indicates whether the instance wants the color chosen
    /// for the item or not. The purpose of this field, which is true if and
    /// only if $\text{COLOR}(x)=-1$ in Knuth's Algorithm C, is to avoid
    /// repeatedly purifying an item; see methods [`purify`] and [`unpurify`]
    /// for details.
    ///
    /// [`purify`]: Solver::purify
    /// [`unpurify`]: Solver::unpurify
    wants_color: bool,
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
        first_in_prev: Option<InstIndex>,
        /// The last node in the succeeding option, or [`None`] if this is
        /// the spacer that comes after the last option.
        ///
        /// This field is an aid to traversing such option in cyclic order,
        /// from right to left.
        last_in_next: Option<InstIndex>,
    },
    /// An instance of an item in some option.
    Instance(Instance<C>),
}

/// Visits all solutions to a given XCC problem by means of dancing links.
///
/// More precisely, this structure embodies an implementation of Algorithm C,
/// as presented by D. E. Knuth in Section 7.2.2.1 of [_TAOCP_ **4B**][taocp4b],
/// part 2, pages 87–91.
///
/// [XCC solver]: `crate::Solver`
/// [taocp4b]: https://www-cs-faculty.stanford.edu/~knuth/taocp.html#vol4
pub struct Solver<'i, I, C> {
    /// The $N=N_1+N_2$ items, some of which are uncovered and consequently
    /// appear in the currently active lists.
    items: Vec<Item<'i, I>>,
    /// The [item instances] within the vertical lists, with [spacers] between
    /// them.
    ///
    /// [item instances]: `Node::Instance`
    /// [spacers]: `Node::Spacer`
    nodes: Vec<Node<C>>,
    /// A stack of item instance pointers used for backtracking.
    pointers: Vec<InstIndex>,
}

impl<'i, I: Eq, C: Eq + Copy> Solver<'i, I, C> {
    // Problem setup routines.

    /// Appends a new node to the vertical list of the specified item.
    ///
    /// If the item is secondary, `color` may specify the color assigned to
    /// the item by the option (if any). Otherwise `color` must be [`None`].
    fn append_inst(&mut self, item_ix: ItemIndex, ix: InstIndex, color: Option<C>) {
        let item = self.item_mut(item_ix);
        item.len += 1;
        let above = if let Some(prev_last_ix) = item.last_option.replace(ix) {
            // Update the `below` link of the new node's predecessor
            // in the vertical list of `item`.
            let prev = self.instance_mut(prev_last_ix);
            prev.below = Some(ix);
            Some(prev_last_ix)
        } else {
            // This is the first option that involves `item`.
            item.first_option = Some(ix);
            None
        };
        self.nodes.push(Node::Instance(Instance {
            item: item_ix,
            above,
            below: None,
            color,
            wants_color: false,
        }));
    }

    // Algorithm C routines.

    /// Marks an item as covered by deleting it from the list of items remaining
    /// to be covered (the horizontal list), and by deleting all of the options
    /// that contain the item from the database of currently active options.
    fn cover(&mut self, ix: ItemIndex) {
        let item = self.item(ix);
        let mut inst_ix = item.first_option;

        // Delete `item` from the horizontal list.
        let (left_ix, right_ix) = (item.left, item.right);
        self.item_mut(left_ix).right = right_ix;
        self.item_mut(right_ix).left = left_ix;

        // Hide all options containing `item`, from top to bottom.
        while let Some(ix) = inst_ix {
            self.hide(ix);
            inst_ix = self.instance(ix).below;
        }
    }

    /// Hides an option that cannot appear in an exact cover for the items
    /// remaining in the horizontal list. This step traverses the colored
    /// siblings both to the left and to the right of the node with index `ix`,
    /// and deletes them from their corresponding vertical lists.
    fn hide(&mut self, ix: InstIndex) {
        // Proceed cyclically through the nodes of the option associated with
        // the given node, from left to right. We store the nodes of an option
        // contiguously in the `self.nodes` arena, so their indices form a
        // sequence of consecutive integers. The end of this sublist is
        // delimited by a spacer node, whose `prev` link points to the node
        // associated with the first item of the option. Thus, to visit the
        // relevant nodes we can start from the node at index `ix` until
        // reaching a spacer node; then we return back to the first item in
        // the option and continue removing the nodes from their vertical lists
        // until reaching the given index `ix`.
        let mut cur_ix = ix.increment();
        while cur_ix != ix {
            cur_ix = match *self.node(cur_ix.get()) {
                Node::Spacer { first_in_prev, .. } => {
                    // Return to the first item in the option.
                    first_in_prev.unwrap()
                }
                Node::Instance(Instance {
                    item,
                    above,
                    below,
                    wants_color,
                    ..
                }) => {
                    // Ignore the node if it already has the "correct" color.
                    if !wants_color {
                        if let Some(above) = above {
                            self.instance_mut(above).below = below;
                        } else {
                            self.item_mut(item).first_option = below;
                        }
                        if let Some(below) = below {
                            self.instance_mut(below).above = above;
                        } else {
                            self.item_mut(item).last_option = above;
                        }
                        // Update the length of the vertical list.
                        self.item_mut(item).len -= 1;
                    }
                    // Continue to go rightwards.
                    cur_ix.increment()
                }
            };
        }
    }

    /// Undoes the updates made by the last [covering](`Self::cover`) operation.
    /// This step puts the item at index `ix` back into the list of items remaining
    /// to be covered (the horizontal list), and reinserts all of the options
    /// that contain the item into the database of currently active options.
    fn uncover(&mut self, ix: ItemIndex) {
        let item = self.item(ix);
        let mut node_ix = item.first_option;

        // Put back `item` into the horizontal list.
        let (left_ix, right_ix) = (item.left, item.right);
        self.item_mut(left_ix).right = ix;
        self.item_mut(right_ix).left = ix;

        // Unhide all options containing `item`, from top to bottom. This order
        // may appear to be incorrect at first glance, because covering is also
        // done from top to bottom. But the answer to exercise 7.2.2.1–2 of
        // TAOCP shows that it is completely trustworthy.
        while let Some(ix) = node_ix {
            self.unhide(ix);
            node_ix = self.instance(ix).below;
        }
    }

    /// Undoes the updates made by the last [hiding](`Self::hide`) operation.
    /// This step visits the colored siblings both to the left and to the right
    /// of the node at index `ix`, and puts them back into their corresponding
    /// vertical lists.
    fn unhide(&mut self, ix: InstIndex) {
        // See `Self::hide` for an explanation. There is an important difference
        // between these two methods, however: since the first spacer cannot
        // be referenced using a `NodeIndex` and we traverse the table of nodes
        // in reverse order, we need to use raw indices.
        let ix = ix.get();
        let mut cur_ix = ix - 1;
        while cur_ix != ix {
            cur_ix = match self.nodes[cur_ix] {
                Node::Spacer { last_in_next, .. } => {
                    // Return to the last item in the option.
                    last_in_next
                        .expect("spacer should have a last_in_next link")
                        .get()
                }
                Node::Instance(Instance {
                    item,
                    above,
                    below,
                    wants_color,
                    ..
                }) => {
                    // Ignore the node if we know that it has the correct color.
                    if !wants_color {
                        // Reinsert `inst` into its vertical list.
                        // SAFETY: `inst` is not a spacer, so `cur_ix > 0`.
                        let wrapped_ix = Some(InstIndex::new(cur_ix));
                        if let Some(above) = above {
                            self.instance_mut(above).below = wrapped_ix;
                        } else {
                            self.item_mut(item).first_option = wrapped_ix;
                        }
                        if let Some(below) = below {
                            self.instance_mut(below).above = wrapped_ix;
                        } else {
                            self.item_mut(item).last_option = wrapped_ix;
                        }
                        // Update the length of the vertical list.
                        self.item_mut(item).len += 1;
                    }
                    // Continue to go leftwards.
                    cur_ix - 1
                }
            };
        }
    }

    /// [Covers](`Self::cover`) the item of an option, if it has no color
    /// preference. Otherwise the given node has a color control, and we
    /// [purify](`Self::purify`) it to remove all options with conflicting
    /// colors from the relevant vertical lists.
    fn commit(&mut self, ix: InstIndex) {
        let inst = self.instance(ix);
        if let Some(color) = inst.color {
            // Don't purify a vertical list that has already been culled.
            if !inst.wants_color {
                self.purify(ix, color);
            }
        } else {
            self.cover(inst.item);
        }
    }

    /// Removes all options that are incompatible with the color constraint
    /// imposed by the given secondary item instance (if it were present in a
    /// solution). The items of all compatible options in the relevant vertical
    /// list temporarily have their `wants_color` field set to `true` in order
    /// to prevent them from being repeatedly purified (because they already
    /// have the "correct" color).
    fn purify(&mut self, ix: InstIndex, color: C) {
        // We cannot use `debug_assert_eq` because `C` need not implement `Debug`.
        debug_assert!(
            self.instance(ix).color == Some(color),
            "item instance has unexpected or missing color control"
        );
        let item_ix = self.instance(ix).item;
        let item = self.item_mut(item_ix);
        item.purified = true;
        // Hide all options that contain the given item but with a color other
        // than `color`, from top to bottom. If an item in the vertical list
        // has the "correct" color, then mark it to avoid its repurification
        // in the future.
        let mut cur_ix = item.first_option;
        while let Some(ix) = cur_ix {
            let inst = self.instance_mut(ix);
            if inst.color == Some(color) {
                inst.wants_color = true; // $\texttt{COLOR}(q)\gets-1$.
            } else {
                self.hide(ix);
            }
            cur_ix = self.instance(ix).below;
        }
    }

    /// Undoes the updates made by the last ["commit"](`Self::commit`) operation.
    /// If the given item is primary, we cover it as in Algorithm X. Otherwise
    /// the item instance has a color control, and we [unpurify](`Self::unpurify`)
    /// by putting back all options with conflicting colors into the relevant
    /// vertical lists.
    fn uncommit(&mut self, ix: InstIndex) {
        let inst = self.instance(ix);
        if let Some(color) = inst.color {
            // Don't unpurify an item that's already known to have the
            // correct color.
            if !inst.wants_color {
                self.unpurify(ix, color);
            }
        } else {
            self.uncover(inst.item);
        }
    }

    /// Undoes the updates made by the last ["purify"](`Self::purify`) operation.
    /// Puts back all the options incompatible with the given secondary item
    /// into the corresponding vertical list, and sets back the color field
    /// of every compatible item instance.
    fn unpurify(&mut self, ix: InstIndex, color: C) {
        // Again, we use `debug_assert` rather than `debug_assert_eq` because
        // `C` might not implement `Debug`.
        debug_assert!(
            self.instance(ix).color == Some(color),
            "item instance has unexpected or missing color control"
        );
        let item_ix = self.instance(ix).item;
        let item = self.item_mut(item_ix);
        item.purified = false;
        // Unhide all options that contain the given item, from bottom to top.
        // If a node in the vertical list has its `wants_color` field set to
        // `true`, we need to reset it.
        let mut cur_ix = item.last_option;
        while let Some(ix) = cur_ix {
            let inst = self.instance_mut(ix);
            if inst.wants_color {
                // $\texttt{COLOR}(q)<0$ in Knuth's description.
                inst.wants_color = false; // $\texttt{COLOR}(q)\gets c`.
            } else {
                self.unhide(ix);
            }
            cur_ix = self.instance(ix).above;
        }
    }

    /// Finds an active primary item $i$ for which $h(i)$ is minimum, where
    /// $h$ is usually a heuristic function intended to reduce the amount of
    /// branching performed by Algorithm C. In case of equality, ties are
    /// broken by using the position of $i$ within the horizontal list of
    /// active primary items.
    ///
    /// Returns `None` if all primary items have been covered.
    fn choose_item<H>(&self, heuristic: H) -> Option<ItemIndex>
    where
        H: Fn(&Item<'i, I>) -> usize,
    {
        let mut min_h = usize::MAX;
        let mut min_ix = None;
        let mut cur_ix = self.primary_head().right;
        while cur_ix != PRIMARY_HEADER {
            let item = self.item(cur_ix);
            let h = heuristic(item);
            if h < min_h {
                // If $h(i)=0$, then $i$ is surely the result.
                if h == 0 {
                    return Some(cur_ix);
                }
                min_h = h;
                min_ix = Some(cur_ix);
            }
            cur_ix = item.right;
        }
        min_ix
    }

    /// Given a node corresponding to the covering of a particular item $i$
    /// with some option $o$, commits all the items $\neq i$ in $o$ from
    /// the lists of active items.
    ///
    /// This function is part of step C5 in Knuth's Algorithm C.
    fn commit_items_of(&mut self, ix: InstIndex) {
        // Commit the items cyclically from left to right.
        let mut cur_ix = ix.increment();
        while cur_ix != ix {
            cur_ix = match self.node(cur_ix.get()) {
                Node::Spacer { first_in_prev, .. } => {
                    first_in_prev.expect("spacer should have a first_in_prev link")
                }
                Node::Instance(_) => {
                    self.commit(cur_ix);
                    cur_ix.increment()
                }
            }
        }
    }

    /// Given a node corresponding to the covering of a particular item $i$
    /// with some option $o$, uncommits all the items $\neq i$ in $o$ back
    /// into the list of items that need to be covered.
    ///
    /// This function is part of step C6 in Knuth's Algorithm C.
    fn uncommit_items_of(&mut self, ix: InstIndex) {
        // Uncommit the items cyclically, in the opposite order as `commit_items_of`.
        // As in `Self::unhide`, we must use raw node indices in case we visit
        // the first spacer.
        let ix = ix.get();
        let mut cur_ix = ix - 1;
        while cur_ix != ix {
            cur_ix = match self.node(cur_ix) {
                Node::Spacer { last_in_next, .. } => last_in_next
                    .expect("spacer should have a last_in_next link")
                    .get(),
                Node::Instance(_) => {
                    self.uncommit(InstIndex::new(cur_ix));
                    cur_ix - 1
                }
            }
        }
    }
}

impl<'i, I: Eq, C: Eq + Copy> crate::Solver<'i, I, C> for Solver<'i, I, C> {
    fn new(primary: &'i [I], secondary: &'i [I]) -> Self {
        // Construct the horizontal list.
        let n_1 = primary.len();
        let n = n_1 + secondary.len();
        let last_primary_ix = ItemIndex::new(n_1);
        let primary_head = Item::header(last_primary_ix, ItemIndex::new(1));
        let first_secondary_ix = last_primary_ix.increment();
        let last_secondary_ix = ItemIndex::new(if secondary.is_empty() { n + 1 } else { n });
        let secondary_head = Item::header(last_secondary_ix, first_secondary_ix);
        let items = primary
            .iter()
            .chain(secondary)
            .enumerate()
            .map(|(prev_ix, label)| {
                let cur_ix = ItemIndex::new(prev_ix + 1);
                // Ensure that no item appears twice in the horizontal list, but
                // only check this invariant in debug mode: We don't require `T`
                // to be bound by `Ord` nor `Hash`, so this operation needs $O(N)$
                // steps per item.
                debug_assert!(
                    // We cannot use `primary[..prev_ix].contains(label)` since
                    // `prev_ix` is out of bounds when the current item is
                    // secondary.
                    !primary.iter().take(prev_ix).any(|o| o == label),
                    "item at index {cur_ix:?} is already in the primary item list"
                );
                debug_assert!(
                    !secondary[..prev_ix.saturating_sub(n_1)].contains(label),
                    "item at index {cur_ix:?} is already in the secondary item list"
                );
                // SAFETY: `cur_ix` does not refer to the header.
                Item::new(label, cur_ix.decrement(), cur_ix.increment())
            });
        let mut items: Vec<Item<'i, I>> = iter::once(primary_head)
            .chain(items)
            .chain(iter::once(secondary_head))
            .collect();
        // Only the primary items appear in the active list:
        if !secondary.is_empty() {
            // 1. Link the first secondary item to the secondary header.
            items[n_1 + 1].left = ItemIndex::new(n + 1);
            // `items[n].right` is already $n_1+1$ by construction.
        }
        // 2. Link the last primary item to the primary header.
        items[n_1].right = PRIMARY_HEADER;
        Self {
            items,
            // Create the node arena, and insert the first spacer.
            nodes: vec![Node::Spacer {
                first_in_prev: None,
                last_in_next: None,
            }],
            pointers: Vec::new(),
        }
    }

    fn add_option<P, S>(&mut self, primary: P, secondary: S)
    where
        P: AsRef<[I]>,
        S: AsRef<[(I, Option<C>)]>,
    {
        let primary = primary.as_ref();
        let secondary = secondary.as_ref();
        // We will create one item instance per item in `primary` and `secondary`,
        // followed by a trailing spacer node.
        self.nodes.reserve(primary.len() + secondary.len() + 1);
        let first_inst_ix = InstIndex::new(self.nodes.len());
        let mut inst_ix = first_inst_ix;
        for (ix, label) in primary.iter().enumerate() {
            // Fail if an item label appears more than once in the option.
            debug_assert!(
                !primary[..ix].contains(label),
                "primary item at index {ix} can only appear once in the option"
            );
            let item_ix = self.find_item(label).unwrap_or_else(|| {
                panic!("primary item at index {ix} must be in the problem's item list");
            });
            // Append the new node to the vertical list of `item`.
            self.append_inst(item_ix, inst_ix, None);
            inst_ix = inst_ix.increment();
        }
        for (ix, inst) in secondary.iter().enumerate() {
            // Fail if an item label appears more than one in the option.
            let (label, color) = inst;
            debug_assert!(
                !primary.contains(label) && !secondary[..ix].contains(inst),
                "secondary item at index {ix} can only appear once in the option"
            );
            let item_ix = self.find_item(label).unwrap_or_else(|| {
                panic!("secondary item at index {ix} must be in the problem's item list");
            });
            // Append the new node to the vertical list of `item`.
            self.append_inst(item_ix, inst_ix, *color);
            inst_ix = inst_ix.increment();
        }
        assert_ne!(first_inst_ix, inst_ix, "option must have at least one item");
        // Link the previous spacer to the last node in the option.
        // The first spacer cannot be referenced directly; see `InstIndex`.
        let prev_spacer = &mut self.nodes[first_inst_ix.get() - 1];
        if let Node::Spacer { last_in_next, .. } = prev_spacer {
            *last_in_next = inst_ix.decrement();
        } else {
            panic!("the record before the first node should be a spacer");
        }
        // Create the next spacer, and link it to the first node in the option.
        self.nodes.push(Node::Spacer {
            first_in_prev: Some(first_inst_ix),
            last_in_next: None,
        })
    }

    fn solve<F>(mut self, mut visit: F)
    where
        F: FnMut(Solution<'_, 'i, I, C, Self>),
    {
        // The heuristic function used in step C3 to choose an active item
        // for branching. Knuth found that selecting an item whose vertical
        // list is of minimum length often works well in practice; this strategy
        // is called the "minimum remaining values" (MRV) heuristic. See
        // Section 7.2.2.3 in [_The Art of Computer Programming_, Pre-Fascicle 7A]
        // for numerous empirical results on standard exact cover problems.
        let branch_heuristic = |i: &Item<'i, I>| i.len;
        'outer: loop {
            // Try to cover as many items as possible, without backtracking.
            loop {
                // C3: Select an item $i$ that needs to be covered.
                if let Some(item_ix) = self.choose_item(branch_heuristic) {
                    // C4: Cover item $i$ using the first action option $x_l$
                    //     in its vertical list.
                    let item = self.item(item_ix);
                    if let Some(inst_ix) = item.first_option {
                        self.cover(item_ix);
                        self.pointers.push(inst_ix);
                        // C5: Commit the items $\neq i$ in the option that
                        //     contains $x_l$, cyclically from left to right.
                        self.commit_items_of(inst_ix);
                    } else {
                        // C7: There are no options left to cover $i$; backtrack.
                        // Optimization: we only cover an item once we know that
                        // there is an active option that contains it. Therefore
                        // the original step in Knuth's algorithm translates to
                        // a no-op here.
                        break;
                    }
                } else {
                    // C2: All primary items have been covered. Visit the solution
                    //     given by the nodes in `self.pointers` and leave the
                    //     current recursion level.
                    if self.is_valid_solution() {
                        visit(Solution {
                            solver: &mut self,
                            level: 0,
                            _phantom: PhantomData,
                        });
                    }
                    break;
                }
            }
            // C8: Leave the current recursion level $l$ until we find an item
            //     that can be covered.
            while let Some(inst_ix) = self.pointers.pop() {
                // C6: In order to cover $i$ (the item associated with $x_l$)
                //     using another option, we need to undo the covering done
                //     by operation C5 above. This amounts to uncommiting the
                //     items $\neq i$ in the option that contains $x_l$,
                //     cyclically from right to left.
                self.uncommit_items_of(inst_ix);
                // Also set the current pointer to the next active option
                // in the vertical list for $i$, if any.
                let inst = self.instance(inst_ix);
                if let Some(below_ix) = inst.below {
                    self.pointers.push(below_ix);
                    // C5: Try to uncommit item $i$ with this new option and
                    //     go back to C2.
                    self.commit_items_of(below_ix);
                    continue 'outer;
                } else {
                    // C5, C7: We have tried all options for $i$; backtrack.
                    self.uncover(inst.item);
                }
            }
            // C8: We have explored the entire search tree; terminate.
            return;
        }
    }
}

impl<'i, I: Eq, C> Solver<'i, I, C> {
    /// Returns whether [`solve`] should visit the current solution.
    ///
    /// A solution is valid only if the (secondary) items in the purely
    /// secondary options are already covered by options containing at least
    /// one primary item. This happens if the vertical lists of all active
    /// nonpurified secondary items are empty, which in turn occurs as
    /// the result of [`hide`] operations during the commiting of items
    /// $\ne i$ in step C5 of Algorithm C.
    ///
    /// [`solve`]: crate::Solver::solve
    /// [`hide`]: Self::hide
    fn is_valid_solution(&self) -> bool {
        // Traverse the horizontal list of active secondary items, checking
        // that their corresponding vertical lists are empty (and thus have
        // already been dealt with by primary covering). Exercise 7.2.2.1–19
        // of TAOCP explains this procedure in more detail.
        let secondary_head_ix = ItemIndex::new(self.items.len() - 1);
        let secondary_head = self.secondary_head();
        let first_active_secondary_ix = secondary_head.right;
        let mut cur_ix = first_active_secondary_ix;
        while cur_ix != secondary_head_ix {
            let item = self.item(cur_ix);
            if !item.purified && item.len > 0 {
                return false; // Skip the solution.
            }
            cur_ix = item.right;
        }
        // We have traversed the entire list of active secondary items;
        // visit the solution.
        true
    }

    // Accessor methods.

    /// Returns a reference to the item at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds.
    fn item(&self, ix: ItemIndex) -> &Item<'i, I> {
        &self.items[ix.get()]
    }

    /// Returns a mutable reference to the item at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds.
    fn item_mut(&mut self, ix: ItemIndex) -> &mut Item<'i, I> {
        &mut self.items[ix.get()]
    }

    /// Returns a reference to the head of the list of primary items
    /// that need to be covered.
    fn primary_head(&self) -> &Item<'i, I> {
        self.item(PRIMARY_HEADER)
    }

    /// Returns a reference to the head of the list of secondary items
    /// that can still be covered.
    fn secondary_head(&self) -> &Item<'i, I> {
        self.items.last().unwrap()
    }

    /// Search through the table of primary and secondary items to find
    /// the node with the given label, if any.
    fn find_item(&self, label: &I) -> Option<ItemIndex> {
        // Remember that `T` is not bound by `Ord` nor `Hash`, so we need to
        // search through the whole `items` list in order to find the node
        // corresponding to `label` in the worst case.
        let mut nodes = self.items.iter().enumerate();
        // Skip the heads of the active item lists.
        nodes.next();
        nodes.next_back();
        nodes
            .find(|(_, item)| {
                // SAFETY: `item` is not a header, so its label is initialized.
                let other_label = unsafe { item.label.assume_init() };
                label == other_label
            })
            .map(|(ix, _)| ItemIndex::new(ix))
    }

    /// Returns a reference to the node at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds.
    fn node(&self, ix: NodeIndex) -> &Node<C> {
        &self.nodes[ix]
    }

    /// Returns a reference to the item instance at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds, or if the node
    /// referenced is a [spacer](`Node::Spacer`) rather than an instance.
    fn instance(&self, ix: InstIndex) -> &Instance<C> {
        if let Node::Instance(inst) = self.node(ix.get()) {
            inst
        } else {
            panic!("node at index {ix:?} is not an item instance")
        }
    }

    /// Returns a mutable reference to the item instance at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds, or if the node
    /// referenced is a [spacer](`Node::Spacer`) rather than an instance.
    fn instance_mut(&mut self, ix: InstIndex) -> &mut Instance<C> {
        if let Node::Instance(inst) = &mut self.nodes[ix.get()] {
            inst
        } else {
            panic!("node at index {ix:?} is not an item instance")
        }
    }
}

impl<'i, I: Eq, C> crate::private::Solver<'i, I, C> for Solver<'i, I, C> {
    fn pointer(&self, level: usize) -> Option<InstIndex> {
        self.pointers.get(level).copied()
    }

    fn level(&self) -> usize {
        self.pointers.len()
    }

    fn option_of(&self, ix: InstIndex, result: &mut Vec<&'i I>) {
        result.clear();
        let mut cur_ix = ix;
        loop {
            cur_ix = match self.node(cur_ix.get()) {
                Node::Spacer { first_in_prev, .. } => {
                    first_in_prev.expect("spacer should have a first_in_prev link")
                }
                Node::Instance(Instance { item, .. }) => {
                    let item = self.item(*item);
                    // SAFETY: `item` is a nonheader node in the item table,
                    // so its label is initialized.
                    result.push(unsafe { item.label.assume_init() });
                    cur_ix.increment()
                }
            };
            if cur_ix == ix {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::indices::ItemIndex;
    use crate::{DlSolver, Solver};
    use std::fmt::Debug;

    fn assert_eq_item<'i, I>(item: &Item<'i, I>, label: &I, left: ItemIndex, right: ItemIndex)
    where
        I: Debug + Eq,
    {
        assert_eq!(unsafe { item.label.assume_init() }, label);
        assert_eq!(item.left, left);
        assert_eq!(item.right, right);
    }

    #[test]
    fn new_exact_cover_with_primary_only() {
        let solver: DlSolver<u8, ()> = DlSolver::new(&[1, 2, 3], &[]);
        assert_eq!(solver.items.len(), 5); // 2 headers + 3 items

        let primary_header = solver.primary_head();
        assert_eq!(primary_header.left, ItemIndex::new(3));
        assert_eq!(primary_header.right, ItemIndex::new(1));

        let one = solver.item(ItemIndex::new(1));
        assert_eq_item(one, &1, PRIMARY_HEADER, ItemIndex::new(2));

        let two = solver.item(ItemIndex::new(2));
        assert_eq_item(two, &2, ItemIndex::new(1), ItemIndex::new(3));

        let three = solver.item(ItemIndex::new(3));
        assert_eq_item(three, &3, ItemIndex::new(2), PRIMARY_HEADER);

        let secondary_header = solver.secondary_head();
        assert_eq!(secondary_header.left, ItemIndex::new(4));
        assert_eq!(secondary_header.right, ItemIndex::new(4));
    }

    #[test]
    fn new_exact_cover_with_primary_and_secondary() {
        let solver: DlSolver<char, ()> = DlSolver::new(&['a', 'b', 'c'], &['d', 'e', 'f']);
        assert_eq!(solver.items.len(), 8); // 2 headers + 6 items

        // The left link of this header points to the last primary item,
        // because the secondary items do not appear in the active list
        // of primary items.
        let primary_header = solver.primary_head();
        assert_eq!(primary_header.left, ItemIndex::new(3));
        assert_eq!(primary_header.right, ItemIndex::new(1));

        let a = solver.item(ItemIndex::new(1));
        assert_eq_item(a, &'a', PRIMARY_HEADER, ItemIndex::new(2));

        let b = solver.item(ItemIndex::new(2));
        assert_eq_item(b, &'b', ItemIndex::new(1), ItemIndex::new(3));

        // The right link of the last primary item points to the primary header.
        let c = solver.item(ItemIndex::new(3));
        assert_eq_item(c, &'c', ItemIndex::new(2), PRIMARY_HEADER);

        // The left link of the first secondary item points to the secondary header.
        let d = solver.item(ItemIndex::new(4));
        assert_eq_item(d, &'d', ItemIndex::new(7), ItemIndex::new(5));

        let e = solver.item(ItemIndex::new(5));
        assert_eq_item(e, &'e', ItemIndex::new(4), ItemIndex::new(6));

        // The right link of the last secondary item points to the secondary header.
        let a = solver.item(ItemIndex::new(6));
        assert_eq_item(a, &'f', ItemIndex::new(5), ItemIndex::new(7));

        // The right link of this header points to the first secondary item.
        let secondary_header = solver.secondary_head();
        assert_eq!(secondary_header.left, ItemIndex::new(6));
        assert_eq!(secondary_header.right, ItemIndex::new(4));
    }

    #[test]
    fn new_exact_cover_without_primary_has_no_solution() {
        // We implement the "second death" method to support purely secondary
        // options; see `DlSolver::is_valid_solution` for details. Of course,
        // Algorithm C visits no solutions because they are all purely secondary.
        let mut solver = DlSolver::new(&[], &[1, 2, 3]);
        solver.add_option([], [(1, None)]);
        solver.add_option([], [(2, Some('A'))]);
        solver.solve(|_| panic!("found solution with purely secondary option"));
    }

    #[test]
    fn find_item() {
        let solver: DlSolver<char, ()> = DlSolver::new(&['a', 'b'], &['c', 'd']);
        assert_eq!(solver.find_item(&'a'), Some(ItemIndex::new(1)));
        assert_eq!(solver.find_item(&'b'), Some(ItemIndex::new(2)));
        assert_eq!(solver.find_item(&'c'), Some(ItemIndex::new(3)));
        assert_eq!(solver.find_item(&'d'), Some(ItemIndex::new(4)));
    }

    #[test]
    fn toy_problem_with_colors() {
        // Example problem taken from Section 7.2.2.1 of TAOCP.
        let primary = ['p', 'q', 'r'];
        let secondary = ['x', 'y'];
        let mut solver = DlSolver::new(&primary, &secondary);
        solver.add_option(['p', 'q'], [('x', None), ('y', Some('A'))]);
        solver.add_option(['p', 'r'], [('x', Some('A')), ('y', None)]);
        solver.add_option(['p'], [('x', Some('B'))]);
        solver.add_option(['q'], [('x', Some('A'))]);
        solver.add_option(['r'], [('y', Some('B'))]);

        let mut count = 0;
        let mut option = Vec::new();
        solver.solve(|mut solution| {
            assert!(solution.next(&mut option));
            assert_eq!(option, &[&'q', &'x']); // x:A
            assert!(solution.next(&mut option));
            assert_eq!(option, &[&'p', &'r', &'x', &'y']); // x:A y:A
            assert!(!solution.next(&mut option));
            count += 1;
        });
        assert_eq!(count, 1);
    }

    #[test]
    fn skips_solutions_with_purely_secondary_options() {
        // A colored variant of the problem from Exercise 7.2.2.1–19 of TAOCP.
        let primary = ['a', 'b'];
        let secondary = ['c', 'd', 'e', 'f', 'g'];
        let mut solver: DlSolver<char, ()> = DlSolver::new(&primary, &secondary);
        solver.add_option([], [('c', None), ('e', None)]); // purely secondary
        solver.add_option(['a'], [('d', None), ('g', None)]);
        solver.add_option(['b'], [('c', None), ('f', None)]);
        solver.add_option(['a'], [('d', None), ('f', None)]);
        solver.add_option(['b'], [('g', None)]);
        solver.add_option([], [('d', None), ('e', None), ('g', None)]); // purely secondary

        let mut count = 0;
        let mut option = Vec::new();
        solver.solve(|mut solution| {
            assert!(solution.next(&mut option));
            assert_eq!(option, &[&'a', &'d', &'g']);
            assert!(solution.next(&mut option));
            assert_eq!(option, &[&'b', &'c', &'f']);
            assert!(!solution.next(&mut option));
            count += 1;
        });
        // Note that 'a d g', 'b g' is not a valid solution, because it does not
        // intersect the purely secondary option 'c e'.
        assert_eq!(count, 1);
    }

    #[test]
    fn solutions_intersect_item_sets_of_purely_secondary_options() {
        let mut solver = DlSolver::new(&['a'], &['b', 'c']);
        solver.add_option(['a'], [('b', Some(1)), ('c', Some(2))]);
        solver.add_option([], [('b', Some(1))]);
        solver.add_option([], [('b', Some(2))]);
        solver.add_option([], [('c', Some(3))]);
        // The three purely secondary options do not appear in any solution. The
        // only solution to the XCC problem consists of option $a b:1 c:2$ alone,
        // because it intersects every purely secondary option.
        let mut count = 0;
        let mut option = Vec::new();
        solver.solve(|mut solution| {
            assert!(solution.next(&mut option));
            assert_eq!(option, &[&'a', &'b', &'c']);
            assert!(!solution.next(&mut option));
            count += 1;
        });
        assert_eq!(count, 1);
    }

    #[test]
    fn skips_solutions_that_do_not_intersect_a_purely_secondary_option() {
        let mut solver = DlSolver::new(&['a'], &['b']);
        solver.add_option(['a'], []);
        solver.add_option([], [('b', Some(1))]);
        // Even if option $a$ covers every primary item exactly once, it does
        // not intersect the purely secondary option $b$.
        solver.solve(|_| panic!("found solution with purely secondary option"));
    }
}
