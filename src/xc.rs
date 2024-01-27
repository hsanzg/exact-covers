use std::iter;
use std::mem::MaybeUninit;

use crate::indices::{ItemIndex, NodeIndex};

/// An item in an [exact cover problem](`ExactCovers`).
struct Item<'l, T> {
    /// The data associated with this item.
    ///
    /// This field roughly corresponds to the `NAME` member in Knuth's
    /// data structure.
    ///
    /// # Invariant
    ///
    /// This variable is initialized provided this item does not represent
    /// the special header node in a horizontal list of [`ExactCovers`].
    label: MaybeUninit<&'l T>,
    /// Possibly the previous item in a (horizontal) list of active items,
    /// in cyclic order. The contents of this variable are preserved when
    /// the item is removed from the linked list. This property makes it
    /// possible to apply the dancing links technique on lists of active
    /// items.
    ///
    /// This field corresponds to the `LLINK` pointer in Knuth's data structure.
    left: ItemIndex,
    /// Possibly the next item in a (horizontal) list of active items,
    /// in cyclic order. The contents of this variable are preserved
    /// when the item is removed from the linked list. (See `self.left`
    /// for details.)
    ///
    /// This field corresponds to the `RLINK` pointer in Knuth's data structure.
    right: ItemIndex,
    /// The first option that contains this item, if any. In other words,
    /// the first node in the vertical list for this item.
    ///
    /// This field corresponds to the `DLINK` pointer in Knuth's data structure.
    ///
    /// # Invariant
    ///
    /// `first_option` is `None` if and only if `last_option` is `None`.
    first_option: Option<NodeIndex>,
    /// The last option that contains this item, if any. In other words,
    /// the last node in the vertical list for this item.
    ///
    /// This field corresponds to the `ULINK` pointer in Knuth's data structure.
    last_option: Option<NodeIndex>,
    /// The number of elements in the vertical list for this item.
    ///
    /// # Invariants
    ///
    /// - `len == 0` if and only if `first_option` and `last_option` are `None`.
    /// - If `len == 1`, then `first_option == last_option`.
    len: usize,
}

impl<'l, T> Item<'l, T> {
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
    fn new(label: &'l T, left: ItemIndex, right: ItemIndex) -> Self {
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

/// The position of the special node in the `self.items` table of
/// [`ExactCovers`] that serves as the head of the list of active
/// primary items.
///
/// The list of active secondary items has its own header node,
/// namely the last element in `self.items`. Its position thus
/// depends on the number of items in the exact cover problem,
/// so this constant has no secondary counterpart.
const PRIMARY_HEADER: ItemIndex = ItemIndex::new(0);

/// An internal node in the toroidal data structure of [`ExactCovers`];
/// each of these nodes represents one [item](`Item`) of an option.
#[derive(Copy, Clone)]
struct Node {
    /// The item associated with this node.
    ///
    /// This field roughly corresponds to the `TOP` field in Knuth's data
    /// structure.
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
}

/// A spacer node between options.
#[derive(Copy, Clone)]
struct Spacer {
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
    /// from right to left. It corresponds to the `DLINK` pointer in
    /// Knuth's data structure.
    last_in_next: Option<NodeIndex>,
}

/// A record in the sequential table of [`ExactCovers`] that either is
/// a separator between the items of two options, or it refers to one
/// of these items.
#[derive(Copy, Clone)]
enum Record {
    /// A spacer between options.
    Spacer(Spacer),
    /// An internal node.
    Node(Node),
}

impl Record {
    /// Creates a spacer node, where `first_in_prev` and `last_in_prev` are
    /// respectively the indices of the first and last nodes in the options
    /// before and after the spacer (if any).
    pub fn spacer(first_in_prev: Option<NodeIndex>, last_in_next: Option<NodeIndex>) -> Self {
        Self::Spacer(Spacer {
            first_in_prev,
            last_in_next,
        })
    }
}

/// Visits all [solutions] to an exact cover problem with $N_1>0$ primary items
/// and $N_2\geq 0$ secondary items.
///
/// See the [crate-level documentation](`crate`) for details.
///
/// # Note
///
/// The solver does not visit any solution containing a purely secondary option
/// (that is, an option that uses no primary items). However, the set of items
/// covered by the options in any visited solution intersects every purely
/// secondary option.
///
/// # Example
///
/// Suppose we want to cover the primary items $a,b,c,d,e,f,g$ using some of
/// the following options:
/// \\[
/// 'c\\;e';\quad'a\\;d\\;g';\quad'b\\;c\\;f';\quad'a\\;d\\;f';\quad'b\\;g';\quad'd\\;e\\;g'.
/// \\]
/// (This toy problem was posed in 2022 by Knuth at the beginning of Section
/// 7.2.2.1 in [_The Art of Computer Programming_, Volume 4B, Part 2][taocp4b].)
/// The following program uses `ExactCovers` to find the unique solution $'a\\;d\\;f';
/// \\;'b\\;g';\\;'c\\;e'$:
///
/// ```
/// use exact_covers::xc::ExactCovers;
///
/// let items = ['a', 'b', 'c', 'd', 'e', 'f', 'g'];
/// let mut solver = ExactCovers::new(&items, &[]);
/// solver.add_option([            &'c',       &'e'           ]);
/// solver.add_option([&'a',             &'d',            &'g']);
/// solver.add_option([      &'b', &'c',             &'f'     ]);
/// solver.add_option([&'a',             &'d',       &'f'     ]);
/// solver.add_option([      &'b',                        &'g']);
/// solver.add_option([                  &'d', &'e',      &'g']);
///
/// // We use an auxiliary table to store the items of an option. The chief
/// // purpose of this reserved storage is to reduce heap allocations when
/// // constructing the solutions to an exact cover problem.
/// let mut option = Vec::new();
/// solver.solve(|mut solution| {
///     assert_eq!(solution.option_count(), 3);
///
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [&'a', &'d', &'f']);
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [&'b', &'g']);
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [&'c', &'e']);
/// });
/// ```
///
/// [solutions]: `ExactCover`
/// [taocp4b]: https://www-cs-faculty.stanford.edu/~knuth/taocp.html#vol4
pub struct ExactCovers<'i, I> {
    /// The $N=N_1+N_2$ items, some of which are uncovered and consequently
    /// appear in the currently active lists.
    items: Vec<Item<'i, I>>,
    /// The [nodes](`Node`) within the vertical lists, with [spacers](`Spacer`)
    /// between them.
    records: Vec<Record>,
    /// A stack of node pointers used for backtracking.
    pointers: Vec<NodeIndex>,
}

impl<'i, I: Eq> ExactCovers<'i, I> {
    // Setup routines.

    /// Creates a solver for an exact cover problem on the given primary
    /// and secondary items.
    ///
    /// To specify the options to cover these items, use [`Self::add_option`].
    ///
    /// # Panics
    ///
    /// This function panics if the list of primary items is empty.
    pub fn new(primary: &'i [I], secondary: &'i [I]) -> Self {
        assert!(
            !primary.is_empty(),
            "problem must have at least one primary item"
        );
        // Construct the horizontal list.
        let n_1 = primary.len();
        let n = primary.len() + secondary.len();
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
            // items[n].right = ItemIndex::new(n_1 + 1);
        }
        // 2. Link the last primary item to the primary header.
        items[n_1].right = PRIMARY_HEADER;
        Self {
            items,
            // Create the node arena, and insert the first spacer.
            records: vec![Record::spacer(None, None)],
            pointers: Vec::new(),
        }
    }

    /// Appends a new node to the vertical list of the specified item.
    fn append_node(&mut self, item_ix: ItemIndex, ix: NodeIndex) {
        let item = self.item_mut(item_ix);
        item.len += 1;
        let above = if let Some(prev_last_ix) = item.last_option.replace(ix) {
            // Update the `below` link of the new node's predecessor
            // in the vertical list of `item`.
            let prev = self.node_mut(prev_last_ix);
            prev.below = Some(ix);
            Some(prev_last_ix)
        } else {
            // This is the first option that involves `item`.
            item.first_option = Some(ix);
            None
        };
        self.records.push(Record::Node(Node {
            item: item_ix,
            above,
            below: None,
        }));
    }

    /// Appends an option to the exact cover problem.
    ///
    /// Once all options have been specified, use [`Self::solve`] to visit
    /// all exact coverings of $I$ with a subset of options in $\mathcal{O}$.
    ///
    /// # Panics
    ///
    /// This function panics if the list of items is empty.
    pub fn add_option<'s, T: AsRef<[&'s I]>>(&'s mut self, items: T) {
        let items = items.as_ref();
        assert!(!items.is_empty(), "option must have at least one item");
        // We will create one node per item in `items` and a trailing spacer.
        self.records.reserve(items.len() + 1);
        let first_node_ix = NodeIndex::new(self.records.len());
        let mut node_ix = first_node_ix;
        for (ix, label) in items.iter().enumerate() {
            // Fail if an item label appears more than once in `items`.
            debug_assert!(
                !items[..ix].contains(label),
                "item at index {ix} can only appear once in `items`"
            );
            let item_ix = self.find_item(label).unwrap_or_else(|| {
                panic!("item at index {ix} of option must be in the problem's item list")
            });
            // Append the new node to the vertical list of `item`.
            self.append_node(item_ix, node_ix);
            node_ix = node_ix.increment();
        }
        // Link the previous spacer to the last node in the option.
        // The first spacer cannot be referenced directly; see `NodeIndex`.
        let prev_spacer = &mut self.records[first_node_ix.get() - 1];
        if let Record::Spacer(Spacer { last_in_next, .. }) = prev_spacer {
            *last_in_next = node_ix.decrement();
        } else {
            panic!("the record before the first node should be a spacer");
        }
        // Create the next spacer, and link it to the first node in the option.
        self.records.push(Record::spacer(Some(first_node_ix), None));
    }

    // Algorithm X routines.

    /// Marks an item as covered by deleting it from the list of items remaining
    /// to be covered (the horizontal list), and by deleting all of the options
    /// that contain from the database of currently active options.
    fn cover(&mut self, ix: ItemIndex) {
        let item = self.item(ix);
        let mut node_ix = item.first_option;

        // Delete `item` from the horizontal list.
        let (left_ix, right_ix) = (item.left, item.right);
        self.item_mut(left_ix).right = right_ix;
        self.item_mut(right_ix).left = left_ix;

        // Hide all options containing `item`, from top to bottom.
        while let Some(ix) = node_ix {
            self.hide(ix);
            node_ix = self.node(ix).below;
        }
    }

    /// Hides an option that cannot appear in an exact cover for the items
    /// remaining in the horizontal list. This step traverses the siblings
    /// both to the left and to the right of the node with index `ix`, and
    /// deletes them from their corresponding vertical lists.
    fn hide(&mut self, ix: NodeIndex) {
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
            cur_ix = match *self.record(cur_ix) {
                Record::Spacer(Spacer { first_in_prev, .. }) => {
                    // Return to the first item in the option.
                    first_in_prev.unwrap()
                }
                Record::Node(Node { item, above, below }) => {
                    if let Some(above) = above {
                        self.node_mut(above).below = below;
                    } else {
                        self.item_mut(item).first_option = below;
                    }
                    if let Some(below) = below {
                        self.node_mut(below).above = above;
                    } else {
                        self.item_mut(item).last_option = above;
                    }
                    // Update the length of the vertical list.
                    self.item_mut(item).len -= 1;
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
        let mut node_ix = item.last_option;

        // Put back `item` into the horizontal list.
        let (left_ix, right_ix) = (item.left, item.right);
        self.item_mut(left_ix).right = ix;
        self.item_mut(right_ix).left = ix;

        // Unhide all options containing `item`, from bottom to top.
        while let Some(ix) = node_ix {
            self.unhide(ix);
            node_ix = self.node(ix).above;
        }
    }

    /// Undoes the updates made by the last [hiding](`Self::hide`) operation.
    /// This step visits the siblings both to the left and to the right of
    /// the node at index `ix`, and puts them back into their corresponding
    /// vertical lists.
    fn unhide(&mut self, ix: NodeIndex) {
        // See `Self::hide` for an explanation. There is an important difference
        // between these two methods, however: since the first spacer cannot
        // be referenced using a `NodeIndex` and we traverse the table of nodes
        // in reverse order, we need to use raw indices.
        let ix = ix.get();
        let mut cur_ix = ix - 1;
        while cur_ix != ix {
            cur_ix = match self.records[cur_ix] {
                Record::Spacer(Spacer { last_in_next, .. }) => {
                    // Return to the last item in the option.
                    last_in_next
                        .expect("spacer should have a last_in_next link")
                        .get()
                }
                Record::Node(Node { item, above, below }) => {
                    // Reinsert `node` into its vertical list.
                    // SAFETY: `node` is not a spacer, so `cur_ix > 0`.
                    let wrapped_ix = Some(NodeIndex::new(cur_ix));
                    if let Some(above) = above {
                        self.node_mut(above).below = wrapped_ix;
                    } else {
                        self.item_mut(item).first_option = wrapped_ix;
                    }
                    if let Some(below) = below {
                        self.node_mut(below).above = wrapped_ix;
                    } else {
                        self.item_mut(item).last_option = wrapped_ix;
                    }
                    // Update the length of the vertical list.
                    self.item_mut(item).len += 1;
                    // Continue to go leftwards.
                    cur_ix - 1
                }
            };
        }
    }

    /// Finds an active primary item $i$ for which $h(i)$ is minimum, where
    /// $h$ is usually a heuristic function intended to reduce the amount of
    /// branching performed by Algorithm X. In case of equality, ties are
    /// broken by using the position of $i$ within the horizontal list of
    /// active primary items.
    ///
    /// Returns `None` if all items have been covered.
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
    /// with some option $o$, deletes all the items $\neq i$ in $o$ from
    /// the lists of active items that have not been covered.
    ///
    /// This function is part of step X5 in Knuth's Algorithm X.
    fn cover_items_of(&mut self, ix: NodeIndex) {
        // Cover the items cyclically from left to right.
        let mut cur_ix = ix.increment();
        while cur_ix != ix {
            cur_ix = match self.record(cur_ix) {
                Record::Spacer(Spacer { first_in_prev, .. }) => {
                    first_in_prev.expect("spacer should have a first_in_prev link")
                }
                Record::Node(Node { item, .. }) => {
                    self.cover(*item);
                    cur_ix.increment()
                }
            }
        }
    }

    /// Given a node corresponding to the covering of a particular item $i$
    /// with some option $o$, inserts all the items $\neq i$ in $o$ back
    /// into the list of items that need to be covered.
    ///
    /// This function is part of step X6 in Knuth's Algorithm X.
    fn uncover_items_of(&mut self, ix: NodeIndex) {
        // Uncover the items cyclically, in the opposite order as `cover_items_of`.
        // As in `Self::unhide`, we must use raw node indices in case we visit
        // the first spacer.
        let ix = ix.get();
        let mut cur_ix = ix - 1;
        while cur_ix != ix {
            cur_ix = match &self.records[cur_ix] {
                Record::Spacer(Spacer { last_in_next, .. }) => last_in_next
                    .expect("spacer should have a last_in_next link")
                    .get(),
                Record::Node(Node { item, .. }) => {
                    self.uncover(*item);
                    cur_ix - 1
                }
            }
        }
    }

    /// Calls a closure on each solution to the constructed exact cover problem.
    pub fn solve<F>(&mut self, mut visit: F)
    where
        F: FnMut(ExactCover<'_, 'i, I>),
    {
        // The heuristic function used in step X3 to choose an active item
        // for branching. Knuth found that selecting an item whose vertical
        // list is of minimum length often works well in practice; this strategy
        // is called the "minimum remaining values" (MRV) heuristic. See
        // Section 7.2.2.3 in [_The Art of Computer Programming_, Pre-Fascicle 7A]
        // for numerous empirical results on standard exact cover problems.
        let branch_heuristic = |i: &Item<'i, I>| i.len;
        'outer: loop {
            // Try to cover as many items as possible, without backtracking.
            loop {
                // X3: Select an item $i$ that needs to be covered.
                if let Some(item_ix) = self.choose_item(branch_heuristic) {
                    // X4: Cover item $i$ using the first action option $x_l$
                    //     in its vertical list.
                    let item = self.item(item_ix);
                    if let Some(node_ix) = item.first_option {
                        self.cover(item_ix);
                        self.pointers.push(node_ix);
                        // X5: Cover the items $\neq i$ in the option that
                        //     contains $x_l$, cyclically from left to right.
                        self.cover_items_of(node_ix);
                    } else {
                        // X7: There are no options left to cover $i$; backtrack.
                        // Optimization: we only cover an item once we know that
                        // there is an active option that contains it. Therefore
                        // the original step in Knuth's algorithm translates to
                        // a no-op here.
                        break;
                    }
                } else {
                    // X2: All items have been covered. Visit the solution given
                    //     by the nodes in `self.pointers` and leave the current
                    //     recursion level.
                    if self.is_valid_solution() {
                        visit(ExactCover {
                            solver: self,
                            level: 0,
                        });
                    }
                    break;
                }
            }
            // X8: Leave the current recursion level $l$ until we find an item
            //     that can be covered.
            while let Some(node_ix) = self.pointers.pop() {
                // X6: In order to cover $i$ (the item associated with $x_l$)
                //     using another option, we need to undo the covering done
                //     by operation X5 above. This amounts to uncovering the
                //     items $\neq i$ in the option that contains $x_l$,
                //     cyclically from right to left.
                self.uncover_items_of(node_ix);
                // Also set the current pointer to the next active option
                // in the vertical list for $i$, if any.
                let node = self.node(node_ix);
                if let Some(below_ix) = node.below {
                    self.pointers.push(below_ix);
                    // X5: Try to cover item $i$ with this new option and
                    //     go back to X2.
                    self.cover_items_of(below_ix);
                    continue 'outer;
                } else {
                    // X5, X7: We have tried all options for $i$; backtrack.
                    self.uncover(node.item);
                }
            }
            // X8: We have explored the entire search tree; terminate.
            return;
        }
    }

    /// Returns whether [`Self::solve`] should visit the current solution.
    ///
    /// A solution is valid only if the (secondary) items in the purely
    /// secondary options are already covered by options containing at least
    /// one primary item. This happens if the vertical lists of all active
    /// secondary items are empty, which in turn occurs as the result of
    /// hide operations during the covering of items $\neq i$ in step X5
    /// of Algorithm X.
    fn is_valid_solution(&self) -> bool {
        // todo: update the following comment.
        // Of course, an option can be purely secondary only if the problem
        // has secondary items. These occupy the last $N_2$ positions of
        // the `self.items` arena.
        // Access the one at the end and traverse the horizontal list of active
        // secondary items.
        let secondary_head_ix = ItemIndex::new(self.items.len() - 1);
        let secondary_head = self.secondary_head();
        let first_active_secondary_ix = secondary_head.right;
        let mut cur_ix = first_active_secondary_ix;
        while cur_ix != secondary_head_ix {
            let item = self.item(cur_ix);
            if item.len > 0 {
                return false; // Skip the solution.
            }
            cur_ix = item.right;
        }
        // We have traversed the entire list of active secondary items;
        // visit the solution.
        true
    }

    // todo: it would be nice to accept any implementor of the `Extend` trait
    // in `option_of`, but there's no way to clear the `result` container
    // prior to inserting the items.

    /// Constructs the option associated with a given node $x$, starting with
    /// the item represented by $x$ and proceeding cyclically from left to
    /// right.
    ///
    /// The resulting sequence of items replaces the previous contents of `results`.
    ///
    /// # Panics
    ///
    /// This function panics if the node index is out of bounds.
    fn option_of(&mut self, ix: NodeIndex, result: &mut Vec<&'i I>) {
        result.clear();
        let mut cur_ix = ix;
        loop {
            cur_ix = match self.record(cur_ix) {
                Record::Spacer(Spacer { first_in_prev, .. }) => {
                    first_in_prev.expect("spacer should have a first_in_prev link")
                }
                Record::Node(Node { item, .. }) => {
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
    fn find_item(&self, label: &'i I) -> Option<ItemIndex> {
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

    /// Returns a reference to the record at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds.
    fn record(&self, ix: NodeIndex) -> &Record {
        &self.records[ix.get()]
    }

    /// Returns a reference to the node at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds, or if the record
    /// referenced is a [spacer](`Record::Spacer`) rather than a node.
    fn node(&self, ix: NodeIndex) -> &Node {
        if let Record::Node(node) = self.record(ix) {
            node
        } else {
            panic!("record at index {ix:?} is not a node")
        }
    }

    /// Returns a mutable reference to the node at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds, or if the record
    /// referenced is a [spacer](`Record::Spacer`) rather than a node.
    fn node_mut(&mut self, ix: NodeIndex) -> &mut Node {
        if let Record::Node(node) = &mut self.records[ix.get()] {
            node
        } else {
            panic!("record at index {ix:?} is not a node")
        }
    }
}

/// An iterator over the options of a solution to an [exact cover problem].
///
/// [exact cover problem]: `ExactCovers`
pub struct ExactCover<'s, 'i: 's, I> {
    /// The solver that found the exact covering.
    solver: &'s mut ExactCovers<'i, I>,
    /// The index of an element in `solver`'s [list of node pointers], which
    /// corresponds to an ancestor of the present solution in the search tree.
    /// The [`Self::next`] function uses this information to reconstruct
    /// the option selected by Algorithm X at that level of recursion.
    ///
    /// [list of node pointers]: `ExactCovers::pointers`
    level: usize,
}

impl<'s, 'i, I: Eq> ExactCover<'s, 'i, I> {
    /// Places the items in the next option of the solution into `result`.
    ///
    /// Returns `false` and leaves the vector untouched if and only if
    /// all options have already been enumerated.
    pub fn next(&mut self, result: &mut Vec<&'i I>) -> bool {
        if let Some(&node_ix) = self.solver.pointers.get(self.level) {
            // Update the recursion depth level and populate `result`.
            self.level += 1;
            self.solver.option_of(node_ix, result);
            true
        } else {
            false
        }
    }

    /// Returns the number of options in the solution.
    pub fn option_count(&self) -> usize {
        self.solver.pointers.len()
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;

    use crate::indices::ItemIndex;
    use crate::xc::Item;

    use super::*;

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
        let solver = ExactCovers::new(&[1, 2, 3], &[]);
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
        let solver = ExactCovers::new(&['a', 'b', 'c'], &['d', 'e', 'f']);
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
    #[should_panic]
    fn new_exact_cover_without_primary_panics() {
        ExactCovers::new(&[], &[1, 2, 3]);
    }

    #[test]
    fn find_item() {
        let solver = ExactCovers::new(&['a', 'b'], &['c', 'd']);
        assert_eq!(solver.find_item(&'a'), Some(ItemIndex::new(1)));
        assert_eq!(solver.find_item(&'b'), Some(ItemIndex::new(2)));
        assert_eq!(solver.find_item(&'c'), Some(ItemIndex::new(3)));
        assert_eq!(solver.find_item(&'d'), Some(ItemIndex::new(4)));
    }

    #[test]
    fn skips_solutions_with_purely_secondary_options() {
        // Example problem taken from Exercise 7.2.2.1.19 of TAOCP.
        let primary = ['a', 'b'];
        let secondary = ['c', 'd', 'e', 'f', 'g'];
        let mut solver = ExactCovers::new(&primary, &secondary);
        solver.add_option([&'c', &'e']); // purely secondary
        solver.add_option([&'a', &'d', &'g']);
        solver.add_option([&'b', &'c', &'f']);
        solver.add_option([&'a', &'d', &'f']);
        solver.add_option([&'b', &'g']);
        solver.add_option([&'d', &'e', &'g']); // purely secondary

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
        assert_eq!(count, 1);
    }
}
