// The following doc comment is kept in sync with the README.md file. Please
// run the `cargo sync-readme` command after modifying the comment contents.
//! This crate provides implementations of D. E. Knuth and C. Solnon's
//! algorithms for solving the exact cover problem with color controls.
//!
//! Suppose we're given a collection $\mathcal{O}$ of _options_, each of which is
//! a set of _items_; the _exact cover_ problem is to find a subcollection
//! $\mathcal{O}^\star\subseteq\mathcal{O}$ of options such that each item occurs
//! in exactly one of $\mathcal{O}^\star$'s options. Knuth proposed a method that
//! achieves this goal in the paper "Dancing Links", [arXiv:cs/0011047][dl] [cs.DS]
//! (2000), whose title refers to a clever yet simple technique for deleting and
//! restoring the nodes of a doubly linked list. His backtracking scheme, called
//! _Algorithm X_, employs this "waltzing" of links to visit all exact covers
//! with options $\mathcal{O}$ in a recursive, depth-first manner. [For further
//! information, see Section 7.2.2.1 of [_The Art of Computer Programming_ 4B (2022)][taocp4b],
//! Part 2, 65--70.]
//!
//! A slight modification of Algorithm X solves the considerably more general
//! problem in which items fall into one of two categories: _primary_ and _secondary_.
//! Now the task is to find a subcollection $\mathcal{O}^\star\subseteq\mathcal{O}$
//! of options that cover every primary item _exactly_ once, while covering every
//! secondary item _at most_ once. The _exact covering with colors_ (XCC) problem
//! arises if we go further and assign a _color_ to the secondary items of each
//! option. Then we say two options are _compatible_ if their secondary items
//! have matching colors, and we define a solution as a collection $\mathcal{O}^\star\subseteq\mathcal{O}$
//! of mutually compatible options that cover every primary item exactly once.
//! (In contrast to the uncolored case, a secondary item can occur in more than
//! one of $\mathcal{O}^\star$'s options provided that their colors are compatible.)
//!
//! Fortunately the dancing links technique is also well suited to XCC problems.
//! Knuth proved this when he introduced Algorithm C in Section 7.2.2.1 of
//! [_TAOCP_ 4B][taocp4b], part 2, pages 87--91; his new procedure extends
//! Algorithm X to colors. In 2020, C. Solnon suggested using the sparse-set
//! data structure of P. Briggs and L. Torczon [[_ACM Letters on Programming Languages and Systems_ 2 (1993)][sparsesets],
//! 59--69] to store the database of currently active options and the list of
//! items that need to be covered. Knuth prepared an implementation of this
//! approach, called the "dancing cells" method, using the conventions of
//! Algorithm C. Numerous benchmark tests for these two XCC solvers appear
//! in Section 7.2.2.3 of [_TAOCP_ 4C (13 January 2023)][taocp4c], Pre-Fascicle
//! 7A (preliminary draft), pages 64--65. To summarize the results of these
//! experiments: there is no clear winner, and we don't yet know a rule for
//! determining which method is best for a particular instance of XCC.
//!
//! This crate is a library of subroutines for color-controlled covering of
//! $N_1\geq 0$ primary items and $N_2\geq 0$ secondary items in the Rust
//! programming language. The following structures are its most important pieces:
//! - [`Problem`] is a representation of an XCC problem that supports simplification
//!   via the removal of _blocking_ and _forcing_. [For a discussion of these
//!   preprocessing operations, see [Knuth, _TAOCP_ 4B (2022)][taocp4b], Part 2,
//!   108--111.]
//! - [`dl::Solver`] finds all solutions to an XCC problem. It implements
//!   a slightly modified form of Knuth's Algorithm 7.2.2.1C.
//! - [`dc::Solver`] adheres to the same input and output conventions as the
//!   previous structure, but it uses the dancing cells technique.
//!
//! Also, the [`examples`] directory contains an instructive set of programs
//! that apply these algorithms to a variety of problems:
//! - [`langford_pairs.rs`] finds all [Langford pairings] of $2n$ numbers.
//! - [`polycube_packing.rs`] computes the number of ways to arrange 25 [Y pentacubes]
//!   in a $5\times 5\times 5$ cuboid.
//! - [`domino_chessboard.rs`] finds all ways to pack 32 dominoes into a chessboard.
//!
//! [dl]: https://arxiv.org/pdf/cs/0011047.pdf
//! [taocp4b]: https://www-cs-faculty.stanford.edu/~knuth/taocp.html#vol4
//! [taocp4c]: https://cs.stanford.edu/~knuth/fasc7a.ps.gz
//! [sparsesets]: https://dl.acm.org/doi/pdf/10.1145/176454.176484
//! [`examples`]: https://github.com/hsanzg/exact-covers/tree/main/examples
//! [`langford_pairs.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/langford_pairs.rs
//! [Langford pairings]: https://en.wikipedia.org/wiki/Langford_pairing
//! [`polycube_packing.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/polycube_packing.rs
//! [Y pentacubes]: https://en.wikipedia.org/wiki/Polycube
//! [`domino_chessboard.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/domino_chessboard.rs

pub mod dc;
pub mod dl;
pub(crate) mod indices;

use crate::dl::{Item, Node};
use crate::indices::{ItemIndex, NodeIndex};
use std::marker::PhantomData;

/// An XCC problem with $N_1\geq 0$ primary items and $N_2\geq 0$ secondary
/// items.
///
/// See the [crate-level documentation](`crate`) for details.
pub struct Problem<'i, I, C> {
    /// The $N=N_1+N_2$ items to cover.
    items: Vec<Item<'i, I>>,
    /// The [nodes] within the vertical lists, with [spacers] between them.
    ///
    /// [nodes]: `Node`
    /// [spacers]: `Node::Spacer`
    nodes: Vec<Node<C>>,
}

impl<'i, I, C> Problem<'i, I, C> {
    /// Creates a new exact cover problem on the given primary and
    /// secondary items.
    ///
    /// To specify the options to cover these items, use [`Self::add_option`].
    pub fn new(primary: &'i [I], secondary: &'i [I]) -> Self {
        // Construct the horizontal lists.
        let n_1 = primary.len();
        let n = n_1 + secondary.len();
        let last_primary_ix = ItemIndex::new(n_1);

        todo!()
    }

    /// Appends an option to the exact cover problem.
    ///
    /// Once all options have been specified, use [`dl::Solver`] or [`dc::Solver`]
    /// to visit all exact coverings of $I$ with a subset of options in $\mathcal{O}$.
    ///
    /// [`dl::Solver`]: `crate::dl::Solver`
    /// [`dc::Solver`]: `crate::dc::Solver`
    pub fn add_option<'s, P, S>(&'s mut self, primary: P, secondary: S)
    where
        P: AsRef<[&'s I]>,
        S: AsRef<[(&'s I, C)]>,
    {
    }
}

/// An iterator over the options of a solution to an [exact cover problem].
///
/// [exact cover problem]: `Problem`
pub struct ExactCover<'s, 'i: 's, I, C, S> {
    /// The solver that found the exact covering.
    solver: &'s mut S,
    /// The index of an element in `solver`'s [list of node pointers], which
    /// corresponds to an ancestor of the present solution in the search tree.
    /// The [`Self::next`] function uses this information to reconstruct the
    /// option selected by the search algorithm at that level of recursion.
    ///
    /// [list of node pointers]: `solver::pointers`
    level: usize,
    _phantom: PhantomData<(&'i I, C)>,
}

impl<'s, 'i, S, I, C> ExactCover<'s, 'i, I, C, S>
where
    S: Solver<'i, I, C>,
    I: Eq,
{
    /// Places the items in the next option of the solution into `result`.
    ///
    /// Returns `false` and leaves the vector untouched if and only if
    /// all options have already been enumerated.
    pub fn next(&mut self, result: &mut Vec<&'i I>) -> bool {
        if let Some(node_ix) = self.solver.pointer(self.level) {
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
        self.solver.depth()
    }
}

/// Visits all [solutions] to an exact cover problem with $N_1\geq 0$
/// primary items and $N_2\geq 0$ secondary items.
///
/// See the [crate-level documentation](`crate`) for details.
///
/// # Notes
///
/// The solver does not visit any solution containing a purely secondary option
/// (that is, an option that uses no primary items). However, the set of items
/// covered by the options in any visited solution intersects every purely
/// secondary option.
///
/// This trait is sealed, meaning that it cannot be implemented outside of the
/// `exact-covers` crate.
///
/// # Example
///
/// Suppose we want to cover the primary items $a,b,c,d,e,f,g$ using some of
/// the following options:
/// \\[
/// 'c\\;e';\quad'a\\;d\\;g';\quad'b\\;c\\;f';\quad'a\\;d\\;f';\quad'b\\;g';\quad'd\\;e\\;g'.
/// \\]
/// (This toy problem was posed by D. E. Knuth at the beginning of Section 7.2.2.1
/// in [_The Art of Computer Programming_ 4B (2022)][taocp4b], Part 2, page 66.)
/// The following program uses an XCC solver based on the dancing links method
/// to find the unique solution $'a\\;d\\;f';\\;'b\\;g';\\;'c\\;e'$:
///
/// ```
/// use exact_covers::Problem;
/// use exact_covers::dl::Solver;
///
/// let items = ['a', 'b', 'c', 'd', 'e', 'f', 'g'];
/// let mut problem = Problem::new(&items, &[]);
/// problem.add_option([            &'c',       &'e'           ], []);
/// problem.add_option([&'a',             &'d',            &'g'], []);
/// problem.add_option([      &'b', &'c',             &'f'     ], []);
/// problem.add_option([&'a',             &'d',       &'f'     ], []);
/// problem.add_option([      &'b',                        &'g'], []);
/// problem.add_option([                  &'d', &'e',      &'g'], []);
///
/// // We use an auxiliary table to store the items of an option. The chief
/// // purpose of this reserved storage is to reduce heap allocations when
/// // constructing the solutions to an exact cover problem.
/// let mut option = Vec::new();
/// let mut solver = Solver::new(problem);
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
pub trait Solver<'i, I, C>: private::Solver<'i, I, C> {
    /// Creates a solver for an exact cover problem.
    fn new(problem: Problem<'i, I, C>) -> Self;

    /// Calls a closure on each solution to the exact cover problem.
    fn solve<F>(&mut self, visit: F)
    where
        F: FnMut(ExactCover<'_, 'i, I, C, Self>);
}

pub(crate) mod private {
    use crate::indices::NodeIndex;

    pub trait Solver<'i, I, C> {
        /// Returns the index of the [instance] in the option selected for
        /// covering the first item covered at the given level of backtracking;
        /// or [`None`], if the search tree is less than `level` levels deep.
        ///
        /// [instance]: `crate::dl::Instance`
        fn pointer(&self, level: usize) -> Option<NodeIndex>;

        /// Returns the current level of the search.
        ///
        /// Returns the current depth $d$ (level $d-1$) of the search tree.
        fn depth(&self) -> usize;

        /// Constructs the option associated with a given [instance node] $x$,
        /// starting with the item represented by $x$ and proceeding cyclically
        /// from left to right.
        ///
        /// The resulting sequence of items replaces the previous contents
        /// of `result`.
        ///
        /// # Panics
        ///
        /// This function panics if the node index is out of bounds.
        ///
        /// [instance node]: `crate::dl::Node::Instance`
        fn option_of(&self, ix: NodeIndex, result: &mut Vec<&'i I>);
    }
}
