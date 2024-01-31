// The following doc comment is kept in sync with the README.md file. Please
// run the `cargo sync-readme` command after modifying the comment contents.
//! This crate provides an implementation of D. E. Knuth's algorithm for solving
//! the exact cover problem with color controls.
//!
//! Suppose we're given a collection $\mathcal{O}$ of _options_, each of which is
//! a set of _items_; the _exact cover_ problem is to find a subcollection
//! $\mathcal{O}^\star\subseteq\mathcal{O}$ of options such that each item occurs
//! in exactly one of $\mathcal{O}^\star$'s options. Knuth proposed a method that
//! achieves this goal in the paper [_Dancing Links_][dl], whose title refers to
//! a clever yet simple technique for deleting and restoring the nodes of a doubly
//! linked list. His backtracking scheme, called _Algorithm X_, employs this "waltzing"
//! of links to visit all exact covers with options $\mathcal{O}$ in a recursive,
//! depth-first manner. [For further information, see Section 7.2.2.1 of
//! [_The Art of Computer Programming_ 4B (2022)][taocp4b], Part 2, 65--70.]
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
//! This crate is a library of subroutines for color-controlled covering of
//! $N_1\geq 0$ primary items and $N_2\geq 0$ secondary items in the Rust
//! programming language. The following structures are its most important pieces:
//! - [`Problem`] is a representation of an XCC problem that supports simplification
//!   via the removal of _blocking_ and _forcing_. [For a discussion of these
//!   preprocessing operations, see [Knuth, _The Art of Computer Programming_ 4B (2022)][taocp4b],
//!   Part 2, 108--111.]
//! - [`Solver`] finds all solutions to an XCC problem.
//!
//! Also, the [`examples`] directory contains an instructive set of programs
//! that apply these algorithms to a variety of problems:
//! - [`langford_pairs.rs`] finds all [Langford pairings] of $2n$ numbers.
//! - [`polycube_packing.rs`] computes the number of ways to arrange 25 [Y pentacubes]
//!   in a $5\times 5\times 5$ cuboid.
//!
//! [dl]: https://arxiv.org/pdf/cs/0011047.pdf
//! [taocp4b]: https://www-cs-faculty.stanford.edu/~knuth/taocp.html#vol4
//! [`examples`]: https://github.com/hsanzg/exact-covers/tree/main/examples
//! [`langford_pairs.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/langford_pairs.rs
//! [Langford pairings]: https://en.wikipedia.org/wiki/Langford_pairing
//! [`polycube_packing.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/polycube_packing.rs
//! [Y pentacubes]: https://en.wikipedia.org/wiki/Polycube

pub(crate) mod indices;
mod problem;
mod solver;

pub use problem::Problem;
pub use solver::Solver;
