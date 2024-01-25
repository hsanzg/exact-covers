# exact-covers

[![Crates.io](https://img.shields.io/crates/v/exact-covers)](https://crates.io/crates/exact-covers)
[![docs.rs](https://img.shields.io/docsrs/exact-covers)](https://docs.rs/exact-covers)
[![Build status](https://github.com/hsanzg/exact-covers/actions/workflows/test.yml/badge.svg)](https://github.com/hsanzg/exact-covers/actions/)

Let $I$ be a set of _items_. Given a collection $\mathcal{O}$ of subsets of $I$,
an _exact cover_ of $I$ is a subcollection $\mathcal{O}^\star$ of $\mathcal{O}$
such that each item in $I$ appears in exactly one _option_ in $\mathcal{O}^\star$.
The goal of an exact cover problem is to find one such subset of options
$\mathcal{O}^\star$.

D. E. Knuth proposed a method for solving the exact cover problem in the paper
[_Dancing Links_][dl], whose title refers to a clever yet simple technique
technique for deleting and restoring the nodes of a doubly linked list.
His backtracking algorithm, called _Algorithm X_, employs this "waltzing"
of links to visit all exact covers of $I$ with options $\mathcal{O}$ in
a recursive, depth-first manner. For further information, see Section 7.2.2.1
of [_The Art of Computer Programming_, Volume 4B, Part 2][taocp4b] (Addison-Wesley,
2022).

A slight modification to this procedure solves the considerably more general
problem in which items fall into one of two categories: _primary_ items,
which _must_ be covered by exactly one option in $\mathcal{O}^\star$, and
_secondary_ items, which _can_ be in at most one option of $\mathcal{O}^\star$.
This crate contains various implementations of Knuth's exact cover solvers
and their data structures in the Rust programming language:
- [`ExactCovers`] finds all exact coverings of $I$ with options in $\mathcal{O}$
  under the assumption that every option contains at least one primary item.
- [`ColoredExactCovers`] will solve the exact cover problem with color constraints.

Also, the [`examples`] directory contains an instructive set of programs that
apply these algorithms to a variety of problems:
- [`langford_pairs.rs`] finds all [Langford pairings] of $2n$ numbers.
- [`polycube_packing.rs`] computes the number of ways to arrange 25 [Y pentacubes]
  in a $5\times 5\times 5$ cuboid. R. Honsberger's book [_Mathematical Gems II_][mgems]
  (1976), Chapter 8, provides a good introduction to the techniques for solving
  polycube packing puzzles.

# License

[MIT](LICENSE) &copy; [Hugo Sanz González](https://hgsg.me)

[dl]: https://arxiv.org/pdf/cs/0011047.pdf
[taocp4b]: https://www-cs-faculty.stanford.edu/~knuth/taocp.html#vol4
[`ExactCovers`]: https://docs.rs/exact-covers/latest/exact-covers/xc/struct.ExactCovers.html
[`ColoredExactCovers`]: https://docs.rs/exact-covers/latest/exact-covers/xcc/struct.ColoredExactCovers.html
[`examples`]: https://github.com/hsanzg/exact-covers/tree/main/examples
[`langford_pairs.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/langford_pairs.rs
[Langford pairings]: https://en.wikipedia.org/wiki/Langford_pairing
[`polycube_packing.rs`]: https://github.com/hsanzg/exact-covers/blob/main/examples/polycube_packing.rs
[Y pentacubes]: https://en.wikipedia.org/wiki/Polycube
[mgems]: https://bookstore.ams.org/dol-2