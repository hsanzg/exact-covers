//! This program determines in how many ways can 32 dominoes fill an $8\times8$
//! chessboard. We set up an exact cover problem with one item for each of the
//! $8\times8=64$ cells, and one option for each of the $2\times8\times7=112$
//! placements of a domino.
//!
//! P. W. Kasteleyn obtained a closed formula for the number of domino coverings
//! of an $m\times n$ rectangle \[_Physica_ **27** (1961), pp. 1209–1225].
//! Interested readers can learn more by working out exercise 7.51 in the second
//! edition of the book _Concrete Mathematics_ (Addison–Wesley, 1994) by R. Graham,
//! D. E. Knuth and O. Patashnik.
use exact_covers::{DlSolver, Solver};
use std::ops::ControlFlow;

/// The number $m$ of rows of the board, also known as _ranks_.
const ROWS: u8 = 8;

/// The number $n$ of columns of the board, also known as _files_.
const COLUMNS: u8 = 8;

fn main() {
    // Generate all cells of an $m\times n$ board.
    let cells: Vec<_> = (0..ROWS)
        .flat_map(|x| (0..COLUMNS).map(move |y| (x, y)))
        .collect();

    let mut solver: DlSolver<_, ()> = DlSolver::new(&cells, &[]);

    // There's an option for each pair of adjacent cells. We start with the
    // $m(n-1)$ horizontal placements,
    for x0 in 0..ROWS {
        for y0 in 0..COLUMNS - 1 {
            solver.add_option([(x0, y0), (x0, y0 + 1)], []);
        }
    }
    // and continue with the $n(m-1)$ vertical ones. To reduce symmetry, insist
    // that the domino occupying the upper left cell is laid out horizontally.
    for y0 in 0..COLUMNS {
        for x0 in (y0 == 0) as u8..ROWS - 1 {
            solver.add_option([(x0, y0), (x0 + 1, y0)], []);
        }
    }

    // Count the number of solutions, taking symmetry into account.
    let mut count = 0;
    solver.solve(|_| {
        count += 2;
        ControlFlow::Continue(())
    });
    assert_eq!(count, 12_988_816);
}
