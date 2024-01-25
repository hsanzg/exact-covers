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
    /// the special header node in the horizontal list of an [`ExactCovers`].
    label: MaybeUninit<&'l T>,
    /// The previous item within the horizontal list, in cyclic order.
    ///
    /// This field corresponds to the `LLINK` pointer in Knuth's data structure.
    left: ItemIndex,
    /// The next item within the horizontal list, in cyclic order.
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
    /// Creates the header for an horizontal list with the specified number
    /// of primary items.
    fn header(primary_count: usize) -> Self {
        assert!(
            primary_count > 0,
            "horizontal list must contain at least one primary item"
        );
        Self {
            label: MaybeUninit::uninit(),
            left: ItemIndex::new(primary_count),
            right: ItemIndex::new(1),
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

/// A node in the toroidal data structure of an [`ExactCovers`].
struct Node {
    /// The item associated with this node, or [`ItemIndex::HEADER`] if
    /// this node is a [spacer](`Self::is_spacer`).
    item: ItemIndex,
    /// The previous node in the vertical list for `item`, if any.
    /// In the case that this node is a [spacer](`Self::is_spacer`), points
    /// to the first node in the preceding option. This is an aid to traversing
    /// such option in cyclic order, from left to right.
    ///
    /// This field corresponds to the `ULINK` pointer in Knuth's data structure,
    /// except that it equals [`None`] instead of `item` when a node belongs
    /// to the first option that contains `item`.
    above: Option<NodeIndex>,
    /// The next node in the vertical list for `item`, if any.
    /// In the case that this node is a [spacer](`Self::is_spacer`), points
    /// to the last node in the succeeding option. This is an aid to traversing
    /// such option in cyclic order, from right to left.
    ///
    /// This field corresponds to the `DLINK` pointer in Knuth's data structure,
    /// except that it equals [`None`] instead of `item` when a node belongs
    /// to the last option that contains `item`.
    below: Option<NodeIndex>,
}

impl Node {
    /// Returns whether this node is a spacer, in which case the [`Self::above`]
    /// and [`Self::below`] links have a special meaning.
    pub fn is_spacer(&self) -> bool {
        self.item == ItemIndex::HEADER
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
    /// The items in the horizontal list.
    items: Vec<Item<'i, I>>,
    /// The nodes within the vertical lists.
    nodes: Vec<Node>,
    /// A stack of node pointers used for backtracking.
    pointers: Vec<NodeIndex>,
    /// Whether the problem has options with no primary items.
    ///
    /// Algorithm X needs to perform a nonnegligible amount of computation
    /// to discard solutions that contain purely secondary options. We keep
    /// track of the presence of these options in `self.items` to see if it
    /// is valid to skip these additional steps.
    has_purely_secondary_options: bool,
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
        let header = iter::once(Item::header(n_1));
        let items = primary
            .iter()
            .chain(secondary)
            .enumerate()
            .map(|(prev_ix, label)| {
                let cur_ix = ItemIndex::new(prev_ix + 1);
                // Ensure that no item appears twice in the horizontal list, but
                // only check this invariant in debug mode: We don't require `T`
                // to be bound by `Ord` nor `Hash`, so this operation needs $O(N)$
                // steps.
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
        let mut items: Vec<Item<'i, I>> = header.chain(items).collect();
        // Only the primary items appear in the active list:
        if !secondary.is_empty() {
            // 1. Link the first secondary item to the last item, and vice versa.
            items[n_1 + 1].left = ItemIndex::new(n);
            items[n].right = ItemIndex::new(n_1 + 1);
        }
        // 2. Link the last primary item to the header (the header already points
        //    to the $N_1$th item thanks to `Item::header`).
        items[n_1].right = ItemIndex::HEADER;
        Self {
            items,
            // Create the node arena, and insert the first spacer.
            nodes: vec![Node {
                item: ItemIndex::HEADER,
                above: None,
                below: None,
            }],
            pointers: Vec::new(),
            has_purely_secondary_options: false,
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
        self.nodes.push(Node {
            item: item_ix,
            above,
            below: None,
        });
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
        self.nodes.reserve(items.len() + 1);
        // Whether the option contains a primary item, and therefore it is not
        // a purely secondary. Warning: this variable is updated only when
        // `self.has_purely_secondary_options` is false, because otherwise
        // we know already that Algorithm X needs to perform the additional
        // computation possibly avoided by this check.
        let mut has_primary = false;
        let first_node_ix = NodeIndex::new(self.nodes.len());
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
            if !self.has_purely_secondary_options {
                if !has_primary && self.is_active(item_ix) {
                    // An item is primary if it appears in the active list.
                    has_primary = true;
                }
            }
            // Append the new node to the vertical list of `item`.
            self.append_node(item_ix, node_ix);
            node_ix = node_ix.increment();
        }
        if !self.has_purely_secondary_options && !has_primary {
            // We just encountered the first purely secondary option.
            self.has_purely_secondary_options = true;
        }
        // Link the previous spacer to the last node in the option.
        // The first spacer cannot be referenced directly; see `NodeIndex`.
        let prev_spacer = &mut self.nodes[first_node_ix.get() - 1];
        prev_spacer.below = node_ix.decrement();
        // Create the next spacer, and link it to the first node in the option.
        self.nodes.push(Node {
            item: ItemIndex::HEADER,
            above: Some(first_node_ix),
            below: None,
        });
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
            let node = self.node(cur_ix);
            if node.is_spacer() {
                // Return to the first item in the option.
                cur_ix = node.above.expect("spacer should have an above link");
            } else {
                // Remove `node` from its vertical list.
                let (above_ix, below_ix) = (node.above, node.below);
                let item_ix = node.item;
                if let Some(above_ix) = above_ix {
                    self.node_mut(above_ix).below = below_ix;
                } else {
                    self.item_mut(item_ix).first_option = below_ix;
                }
                if let Some(below_ix) = below_ix {
                    self.node_mut(below_ix).above = above_ix;
                } else {
                    self.item_mut(item_ix).last_option = above_ix;
                }
                // Update the length of the vertical list.
                self.item_mut(item_ix).len -= 1;
                // Continue to go rightwards.
                cur_ix = cur_ix.increment();
            }
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
            let node = &self.nodes[cur_ix];
            if node.is_spacer() {
                // Return to the last item in the option.
                cur_ix = node.below.expect("spacer should have a below link").get();
            } else {
                // Reinsert `node` into its vertical list.
                let (above_ix, below_ix) = (node.above, node.below);
                let item_ix = node.item;
                // SAFETY: `node` is not a spacer, so `cur_ix > 0`.
                let wrapped_ix = Some(NodeIndex::new(cur_ix));
                if let Some(below_ix) = below_ix {
                    self.node_mut(below_ix).above = wrapped_ix;
                } else {
                    self.item_mut(item_ix).last_option = wrapped_ix;
                }
                if let Some(above_ix) = above_ix {
                    self.node_mut(above_ix).below = wrapped_ix;
                } else {
                    self.item_mut(item_ix).first_option = wrapped_ix;
                }
                // Update the length of the vertical list.
                self.item_mut(item_ix).len += 1;
                // Continue to go leftwards.
                cur_ix -= 1;
            }
        }
    }

    /// Finds an active item $i$ for which $h(i)$ is minimum, where $h$
    /// is usually a heuristic function intended to reduce the amount of
    /// branching performed by Algorithm X. In case of equality, ties are
    /// broken by using the position of $i$ within the horizontal list.
    ///
    /// Returns `None` if all items have been covered.
    fn choose_item<H>(&self, heuristic: H) -> Option<ItemIndex>
    where
        H: Fn(&Item<'i, I>) -> usize,
    {
        let mut min_h = usize::MAX;
        let mut min_ix = None;
        let mut cur_ix = self.header().right;
        while cur_ix != ItemIndex::HEADER {
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
    /// the list of items that need to be covered.
    ///
    /// This function is part of step X5 in Knuth's Algorithm X.
    fn cover_items_of(&mut self, ix: NodeIndex) {
        // Cover the items cyclically from left to right.
        let mut cur_ix = ix.increment();
        while cur_ix != ix {
            let node = self.node(cur_ix);
            if node.is_spacer() {
                cur_ix = node.above.expect("spacer should have an above link");
            } else {
                self.cover(node.item);
                cur_ix = cur_ix.increment();
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
            let node = &self.nodes[cur_ix];
            if node.is_spacer() {
                cur_ix = node.below.expect("spacer should have a below link").get();
            } else {
                self.uncover(node.item);
                cur_ix -= 1;
            }
        }
    }

    /// Calls a closure on each solution to the constructed exact cover problem.
    pub fn solve<F>(&mut self, mut visit: F)
    where
        F: FnMut(ExactCover<'_, 'i, I>),
    {
        // let mut solution_cache = Vec::new();
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
        if !self.has_purely_secondary_options {
            return true;
        }
        // Of course, an option can be purely secondary only if the problem
        // has secondary items. These occupy the last $N_2$ positions of
        // the `self.items` arena. Access the one at the end and traverse
        // the horizontal list of active secondary items.
        let last_secondary_ix = ItemIndex::new(self.items.len() - 1);
        let mut cur_ix = last_secondary_ix;
        loop {
            let item = self.item(cur_ix);
            if item.len > 0 {
                return false; // Skip the solution.
            }
            cur_ix = item.right;
            if last_secondary_ix == cur_ix {
                // We have traversed the entire list of active
                // secondary items; visit the solution.
                return true;
            }
        }
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
            let node = self.node(cur_ix);
            if node.is_spacer() {
                cur_ix = node.above.expect("spacer should have an above link");
            } else {
                let item = self.item(node.item);
                // SAFETY: `node.item` points to a nonheader node in the item
                // table, so its label is initialized.
                result.push(unsafe { item.label.assume_init() });
                cur_ix = cur_ix.increment();
            }
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

    /// Returns a reference to the header of the horizontal list.
    fn header(&self) -> &Item<'i, I> {
        self.item(ItemIndex::HEADER)
    }

    /// Search through the table of primary and secondary items to find the node
    /// with the given label, if any.
    fn find_item(&self, label: &'i I) -> Option<ItemIndex> {
        // Remember that `T` is not bound by `Ord` nor `Hash`, so we need to
        // search through the whole `items` list in order to find the node
        // corresponding to `label` in the worst case.
        self.items
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, item)| {
                // SAFETY: `item` is not the header, so its label is initialized.
                let other_label = unsafe { item.label.assume_init() };
                label == other_label
            })
            .map(|(ix, _)| ItemIndex::new(ix))
    }

    /// Returns whether the item at the given position appears in the active
    /// list, and thus is a primary item.
    ///
    /// # Panics
    ///
    /// This function panics if the item index is out of bounds.
    fn is_active(&self, ix: ItemIndex) -> bool {
        assert!(ix.get() < self.items.len(), "index out of bounds");
        // An item is in the active list if there is a chain of pointers
        // that connects the header and `item`.
        let mut cur_ix = self.header().right;
        while cur_ix != ItemIndex::HEADER {
            if cur_ix == ix {
                return true;
            }
            cur_ix = self.item(cur_ix).right;
        }
        false
    }

    /// Returns a reference to the node at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds.
    fn node(&self, ix: NodeIndex) -> &Node {
        &self.nodes[ix.get()]
    }

    /// Returns a mutable reference to the node at the given position.
    ///
    /// # Panics
    ///
    /// This function panics if the index is out of bounds.
    fn node_mut(&mut self, ix: NodeIndex) -> &mut Node {
        &mut self.nodes[ix.get()]
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
        assert_eq!(solver.items.len(), 4); // header + 3 items

        let header = solver.header();
        assert_eq!(header.left, ItemIndex::new(3));
        assert_eq!(header.right, ItemIndex::new(1));

        let one = solver.item(ItemIndex::new(1));
        assert_eq_item(one, &1, ItemIndex::HEADER, ItemIndex::new(2));

        let two = solver.item(ItemIndex::new(2));
        assert_eq_item(two, &2, ItemIndex::new(1), ItemIndex::new(3));

        let three = solver.item(ItemIndex::new(3));
        assert_eq_item(three, &3, ItemIndex::new(2), ItemIndex::HEADER);
    }

    #[test]
    fn new_exact_cover_with_primary_and_secondary() {
        let solver = ExactCovers::new(&['a', 'b', 'c'], &['d', 'e', 'f']);
        assert_eq!(solver.items.len(), 7); // header + 6 items

        // The left link of the header points to the last primary item,
        // because the secondary items do not appear in the active list.
        let header = solver.header();
        assert_eq!(header.left, ItemIndex::new(3));
        assert_eq!(header.right, ItemIndex::new(1));

        let a = solver.item(ItemIndex::new(1));
        assert_eq_item(a, &'a', ItemIndex::HEADER, ItemIndex::new(2));

        let b = solver.item(ItemIndex::new(2));
        assert_eq_item(b, &'b', ItemIndex::new(1), ItemIndex::new(3));

        // The right link of the last primary item points to the header.
        let c = solver.item(ItemIndex::new(3));
        assert_eq_item(c, &'c', ItemIndex::new(2), ItemIndex::HEADER);

        // The left link of the first secondary item points to the last secondary one.
        let d = solver.item(ItemIndex::new(4));
        assert_eq_item(d, &'d', ItemIndex::new(6), ItemIndex::new(5));

        let e = solver.item(ItemIndex::new(5));
        assert_eq_item(e, &'e', ItemIndex::new(4), ItemIndex::new(6));

        // The right link of the last secondary item points to the first secondary one.
        let a = solver.item(ItemIndex::new(6));
        assert_eq_item(a, &'f', ItemIndex::new(5), ItemIndex::new(4));
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

        assert!(solver.is_active(ItemIndex::new(1)));
        assert!(solver.is_active(ItemIndex::new(2)));
        assert!(!solver.is_active(ItemIndex::new(3)));
        assert!(!solver.is_active(ItemIndex::new(4)));
    }

    #[test]
    #[should_panic]
    fn out_of_bounds_is_active() {
        let solver = ExactCovers::new(&[1, 2], &[]);
        solver.is_active(ItemIndex::new(3));
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
            // assert_eq!(option, &[&'a', &'d', &'g']);
            println!("{option:?}");
            assert!(solution.next(&mut option));
            // assert_eq!(option, &[&'b', &'c', &'f']);
            println!("{option:?}");
            assert!(!solution.next(&mut option));
            count += 1;
            println!("---");
        });
        assert_eq!(count, 1);
    }
}
