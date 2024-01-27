//! Chapter 8 of R. Honsberger's book [_Mathematical Gems II_][mgems] (1976)
//! provides a good introduction to the techniques for solving polycube packing
//! puzzles.
//!
//! [mgems]: https://bookstore.ams.org/dol-2

use exact_covers::xc::ExactCovers;

fn main() {
    let solver = ExactCovers::new(&[1], &[2]);
}
