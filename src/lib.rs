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
//! information, see Section 7.2.2.1 of [_The Art of Computer Programming_ **4B** (2022)][taocp4b],
//! Part 2, 65–70.]
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
//! [_TAOCP_ **4B**][taocp4b], part 2, pages 87–91; his new procedure extends
//! Algorithm X to colors. In 2020, C. Solnon suggested using the sparse-set
//! data structure of P. Briggs and L. Torczon [[_ACM Letters on Programming Languages and Systems_ **2** (1993)][sparsesets],
//! 59–69] to store the database of currently active options and the list of
//! items that need to be covered. Knuth prepared an implementation of this
//! approach, called the "dancing cells" method, using the conventions of
//! Algorithm C. Numerous benchmark tests for these two XCC solvers appear
//! in Section 7.2.2.3 of [_TAOCP_ **4C** (June 25, 2024)][taocp4c], Pre-Fascicle
//! 7A (preliminary draft), pages 64–65. To summarize the results of these
//! experiments: there is no clear winner, and we don't yet know a rule for
//! determining which method is best for a particular instance of XCC.
//!
//! This crate is a library of subroutines for color-controlled covering of
//! $N_1\ge0$ primary items and $N_2\ge0$ secondary items in the Rust
//! programming language. The following structures are its most important pieces:
//! - [`DlSolver`] finds all solutions to an XCC problem. It implements
//!   a slightly modified form of Knuth's Algorithm 7.2.2.1C.
//! - [`DcSolver`] adheres to the same input and output conventions as the
//!   previous structure, but it uses the dancing cells technique.
//!
//! Both implementations support option simplification via the removal of
//! _blocking_ and _forcing_. [For a discussion of these preprocessing operations,
//! see [Knuth, _TAOCP_ **4B** (2022)][taocp4b], Part 2, 108–111.]
//!
//! Also, the [`examples`] directory contains an instructive set of programs
//! that apply these algorithms to a variety of problems:
//! - [`langford_pairs.rs`] finds all [Langford pairings] of $2n$ numbers.
//! - [`polycube_packing.rs`] computes the number of ways to arrange 25 [Y pentacubes]
//!   in a $5\times5\times5$ cuboid.
//! - [`domino_chessboard.rs`] finds all ways to pack 32 dominoes into a chessboard.
//! - [`graceful.rs`] finds all [graceful labelings] of an undirected graph.
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
//! [`graceful.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/graceful.rs
//! [graceful labelings]: https://en.wikipedia.org/wiki/Graceful_labeling

mod dc;
mod dl;
mod indices;

pub use dc::Solver as DcSolver;
pub use dl::Solver as DlSolver;
use std::marker::PhantomData;
use std::ops::ControlFlow;

/// Visits all [solutions] to an XCC problem with $N_1\ge0$ primary items and
/// $N_2\ge0$ secondary items.
///
/// See the [crate-level documentation](`crate`) for details.
///
/// # Notes
///
/// The solver does not visit any solution containing a purely secondary option
/// (that is, an option that uses no primary items). However, the set of items
/// covered by the options in any visited solution intersects every purely
/// secondary option. This strategy is a generalized version of the "second
/// death" method from exercise 7.2.2.1–19 of TAOCP to the XCC problem.
///
/// This trait is sealed, meaning that it cannot be implemented outside of the
/// `exact-covers` crate.
///
/// # Examples
///
/// Suppose we want to cover the primary items $a,b,c,d,e,f,g$ using some of
/// the following options:
/// \\[
/// \`c\\;e';\quad\`a\\;d\\;g';\quad\`b\\;c\\;f';\quad\`a\\;d\\;f';\quad\`b\\;g';\quad\`d\\;e\\;g'.
/// \\]
/// (D. E. Knuth posed this toy problem at the beginning of Section 7.2.2.1
/// in [_The Art of Computer Programming_ **4B** (2022)][taocp4b], Part 2, page 66.)
/// The following program uses an XC solver based on the dancing links method
/// to find the unique solution $\`a\\;d\\;f';\\;\`b\\;g';\\;\`c\\;e'$:
///
/// ```
/// use std::ops::ControlFlow;
/// use exact_covers::{DlSolver, Solver};
///
/// let items = ['a', 'b', 'c', 'd', 'e', 'f', 'g'];
/// let mut solver: DlSolver<char, ()> = DlSolver::new(&items, &[]);
/// solver.add_option([          'c',      'e'         ], []);
/// solver.add_option(['a',           'd',          'g'], []);
/// solver.add_option([     'b', 'c',           'f'    ], []);
/// solver.add_option(['a',           'd',      'f'    ], []);
/// solver.add_option([     'b',                    'g'], []);
/// solver.add_option([               'd', 'e',     'g'], []);
///
/// // We use an auxiliary table to store the items of an option. The chief
/// // purpose of this reserved storage is to reduce heap allocations when
/// // constructing the solutions to an XCC problem.
/// let mut option = Vec::new();
/// solver.solve(|mut solution| {
///     assert_eq!(solution.option_count(), 3);
///
///     // An option is represented as a list of `(item, color)` pairs.
///     // In this example we are not doing color-controlled covering,
///     // so all color assignments are `None`.
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [(&'a', None), (&'d', None), (&'f', None)]);
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [(&'b', None), (&'g', None)]);
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [(&'c', None), (&'e', None)]);
///     ControlFlow::Continue(())
/// });
/// ```
///
/// Here's a slightly more interesting challenge: Given primary items $a,b,c$
/// and secondary items $p,q$, find all subsets of options
/// \\[
/// \`a\\;c\\;p\\;q{:}0';\quad\`b\\;c\\;q{:}2';\quad\`a\\;p';\quad\`b\\;p{:}1';\quad\`q{:}2'
/// \\]
/// that (i) cover every primary item exactly once, and (ii) assign at most one
/// color to every secondary item. (The notation $i{:}x$ means that color $x$ is
/// assigned to item $i$; when a secondary item is not followed by a colon, it
/// is implicitly assigned a unique color which is incompatible with any other.)
/// The program below uses an XCC solver to obtain the solution $\`a\\;p';\\;\`b\\;c\\;q{:}2'$.
/// Observe that the solver discards the only other solution $\`a\\;p';\\;\`b\\;c\\;q{:}2';\\;\`q{:}2'$,
/// because it contains a purely secondary option.
///
/// ```
/// use std::ops::ControlFlow;
/// use exact_covers::{DlSolver, Solver};
///
/// let primary = ['a', 'b', 'c'];
/// let secondary = ['p', 'q'];
/// let mut solver: DlSolver<char, u8> = DlSolver::new(&primary, &secondary);
/// solver.add_option(['a',      'c'], [('p', None),    ('q', Some(0))]);
/// solver.add_option([     'b', 'c'], [                ('q', Some(2))]);
/// solver.add_option(['a'          ], [('p', None)                   ]);
/// solver.add_option([     'b',    ], [('p', Some(1))                ]);
/// solver.add_option([             ], [                ('q', Some(2))]);
///
/// let mut option = Vec::new();
/// let mut num_sols = 0;
/// solver.solve(|mut solution| {
///     // Notice that `color = None` if and only if `item` is primary
///     // or was not explicitly assigned a color by `option`.
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [(&'a', None), (&'p', None)]);
///     assert!(solution.next(&mut option));
///     assert_eq!(option, [(&'b', None), (&'c', None), (&'q', Some(2))]);
///     assert!(!solution.next(&mut option));
///     num_sols += 1;
///     ControlFlow::Continue(())
/// });
/// assert_eq!(num_sols, 1);
/// ```
///
/// [solutions]: `Solution`
/// [`add_option`]: Self::add_option
/// [taocp4b]: https://www-cs-faculty.stanford.edu/~knuth/taocp.html#vol4
// todo: Hopefully some day we will be able to specify the `()` default type
//       parameter for `C`, which e.g. would allow us to remove the annoying
//       type annotation for `solver` above. As it stands, however, type inference
//       in Rust does not use type defaults (see https://github.com/rust-lang/rust/issues/36980#issuecomment-251726254,
//       https://github.com/rust-lang/reference/issues/636 and https://internals.rust-lang.org/t/interaction-of-user-defined-and-integral-fallbacks-with-inference/2496).
pub trait Solver<'i, I, C>: private::Solver<'i, I, C> {
    /// Creates a solver for an XCC problem on the given primary and secondary
    /// items.
    ///
    /// To specify the options to cover these items, use [`Self::add_option`].
    fn new(primary: &'i [I], secondary: &'i [I]) -> Self;

    /// Appends an option to the XCC problem.
    ///
    /// The meaning of a pair $(i,c)$ in the list of secondary items depends on
    /// the value of $c$: If $c$ is `Some(c')` for some `c'`, then the secondary
    /// item $i$ is assigned color `c'`; otherwise $i$ is implicitly assigned
    /// a unique color that doesn't match the color of the item in any other
    /// option.
    ///
    /// Once all options have been specified, use [`Self::solve`] to visit all
    /// solutions to the problem.
    fn add_option<P, S>(&mut self, primary: P, secondary: S)
    where
        P: AsRef<[I]>,
        S: AsRef<[(I, Option<C>)]>;

    /// Calls a closure on each solution to the XCC problem.
    ///
    /// The solution process continues until the closure returns
    /// [`ControlFlow::Break`] or all solutions have been visited,
    /// whichever occurs first.
    fn solve<F>(self, visit: F)
    where
        F: FnMut(Solution<'_, 'i, I, C, Self>) -> ControlFlow<()>;
}

pub(crate) mod private {
    use crate::indices::InstIndex;

    pub trait Solver<'i, I, C> {
        /// Returns the index of the [instance] in the option selected for
        /// covering the first item covered at the given level of backtracking;
        /// or [`None`], if the search tree is less than `level` levels deep.
        ///
        /// [instance]: crate::dl::Instance
        fn pointer(&self, level: usize) -> Option<InstIndex>;

        /// Returns the current level of the search.
        fn level(&self) -> usize;

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
        /// [instance node]: crate::dl::Node::Instance
        fn option_of(&self, ix: InstIndex, result: &mut Vec<(&'i I, Option<C>)>);
    }
}

/// An iterator over the options of a solution to an XCC problem.
pub struct Solution<'s, 'i: 's, I, C, S> {
    /// The solver that found the colored covering.
    solver: &'s mut S,
    /// The index of an element in `solver`'s [list of node pointers], which
    /// corresponds to an ancestor of the present solution in the search tree.
    /// The [`Self::next`] function uses this information to reconstruct the
    /// option selected by the search algorithm at that level of recursion.
    ///
    /// [list of node pointers]: private::Solver::pointer
    level: usize,
    _phantom: PhantomData<(&'i I, C)>,
}

impl<'s, 'i, S, I, C> Solution<'s, 'i, I, C, S>
where
    S: Solver<'i, I, C>,
    I: Eq,
{
    /// Places the items in the next option of the solution and their
    /// color assignments under that same option into `result`.
    ///
    /// Returns `false` and leaves the vector untouched if and only if
    /// all options have already been enumerated.
    pub fn next(&mut self, result: &mut Vec<(&'i I, Option<C>)>) -> bool {
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
        self.solver.level()
    }
}
