#[path = "common/polycubes.rs"]
mod polycubes;

use exact_covers::{DlSolver, Solution, Solver};
use polycubes::{Polycube, Pos};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ops::ControlFlow;
use std::{array, iter};

fn cartesian_prod<T, I, J>(a: I, b: J) -> impl Iterator<Item = [T; 2]> + Clone
where
  T: Clone,
  I: Iterator<Item = T> + Clone,
  J: Iterator<Item = T> + Clone,
{
  a.flat_map(move |x| b.clone().map(move |y| [x.clone(), y]))
}

fn touches<const N: usize>(pc: &Polycube<N>) -> HashMap<Pos<N>, bool> {
  let mut ts = HashMap::new();
  for c in pc.cubies() {
    // Iterate over the neighbors of $c$.
    let mut d = [-1i8; N];
    loop {
      if d.iter().any(|&d| d != 0) {
        let t = array::from_fn(|i| c[i] + d[i]);
        let diag = d.iter().all(|&d| d != 0);
        ts.entry(t).and_modify(|e| *e &= diag).or_insert(diag);
      }
      let mut j = 0;
      while j < N && d[j] == 1 {
        d[j] = -1;
        j += 1;
      }
      if j == N {
        break;
      }
      d[j] += 1;
    }
  }
  // Exclude the cells occupied by the tromino itself.
  for c in pc.cubies() {
    ts.remove(c);
  }
  ts
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Color {
  Orange,
  Pink,
  Blue,
}

fn colors() -> [Color; 3] {
  [Color::Orange, Color::Pink, Color::Blue]
}

impl From<Color> for char {
  fn from(c: Color) -> Self {
    match c {
      Color::Orange => 'o',
      Color::Pink => 'p',
      Color::Blue => 'b',
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Item {
  // Primary.
  Occupy(Pos<2>),
  // Secondary.
  Claim(Pos<2>, Color),
  Empty,
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum ClaimKind {
  Taken,
  Touching,
}

/// Should there be at most one pair of trominoes touching at $v$?
const SINGLE_DIAG_ADJ: bool = true;

pub fn main() {
  const M: u8 = 8;
  const N: u8 = 8;

  let cells = cartesian_prod(0..M as i8, 0..N as i8);
  let occup: Vec<_> = cells.clone().map(Item::Occupy).collect();
  let touch = cells
    .clone()
    .flat_map(|p| colors().map(move |c| Item::Claim(p, c)));
  let sec: Vec<_> = touch.chain(iter::once(Item::Empty)).collect();

  let bent = Polycube::from([[0, 0], [0, 1], [1, 0]]);
  let placements = bent.base_placements();

  let vs = (1..=M.div_ceil(2) as i8)
    .flat_map(|y| (1..=y.min(N.div_ceil(2) as i8)).map(move |x| [x, y]))
    .skip(1); // $(1, 1)$.

  for [vx, vy] in vs {
    let mut solver = DlSolver::new(&occup, &sec);
    for shape in &placements {
      for [x0, y0] in cartesian_prod(0..M as i8 - 1, 0..N as i8 - 1) {
        let pc = shape.transform(|[x, y]| [x0 + x, y0 + y]);

        let mut ts = touches(&pc);
        ts.retain(|&[x, y], _| 0 <= x && x < N as i8 && 0 <= y && y < M as i8);
        for [dx, dy] in cartesian_prod(-1..=0, -1..=0) {
          let c = [vx + dx, vy + dy];
          if let Entry::Occupied(o) = ts.entry(c)
            && *o.get()
          {
            o.remove();
          }
        }

        // To break symmetry, force the trominoes occupying cells
        // $0,0$ and $0,2$ to have specific (distinct) colors.
        let cs: &[_] = match (x0, y0) {
          (0, 0) => &[Color::Orange],
          (0, 1) | (0, 2) => &[Color::Blue],
          _ => &colors(),
        };

        for &c in cs {
          let occup: Vec<_> = pc.cubies().iter().copied().map(Item::Occupy).collect();

          let taken = pc
            .cubies()
            .iter()
            .copied()
            .map(|p| (Item::Claim(p, c), Some(ClaimKind::Taken)));
          let touch = ts
            .keys()
            .copied()
            .map(|p| (Item::Claim(p, c), Some(ClaimKind::Touching)));
          let claims: Vec<_> = taken.chain(touch).collect();

          solver.add_option(&occup, &claims);
        }
      }
    }

    // Add options to cover the empty cell.
    assert_eq!(M * N % 3, 1); // todo: generalize.
    for c in cells.clone() {
      solver.add_option(&[Item::Occupy(c)], &[(Item::Empty, None)]);
    }

    println!("solving for vertex ({vx}, {vy})");
    let mut opts = Vec::new();
    let mut c = 0;
    solver.solve(|mut sol| {
      let board = parse_board::<_, { M as usize }, { N as usize }>(&mut sol, &mut opts);

      // At most two trominoes of the same color may touch diagonally,
      // if `SINGLE_DIAG_ADJ` is true. Otherwise $v$ may be surrounded
      // by up to two pairs of trominoes of the same color.
      let (vx, vy) = (vx as usize, vy as usize);
      if SINGLE_DIAG_ADJ
        && board[vy - 1][vx - 1] == board[vy][vx]
        && board[vy][vx - 1] == board[vy - 1][vx]
      {
        return ControlFlow::Continue(());
      }

      // There are the same number of trominoes of each color.
      let exp_cubies = M * N / 3;
      if !colors().into_iter().all(|q| {
        board
          .as_flattened()
          .iter()
          .filter(|&&c| c == Some(q))
          .count()
          == exp_cubies as usize
      }) {
        return ControlFlow::Continue(());
      }

      // We found a valid solution!
      print_board(board);
      c += 1;
      ControlFlow::Continue(())
    });
    println!("found {c} sols!");
  }
}

fn parse_board<'i, S, const M: usize, const N: usize>(
  sol: &mut Solution<'_, 'i, Item, ClaimKind, S>,
  mut opts: &mut Vec<(&'i Item, Option<ClaimKind>)>,
) -> [[Option<Color>; N]; M]
where
  S: Solver<'i, Item, ClaimKind>,
{
  let mut b = array::repeat(array::repeat(None));
  while sol.next(&mut opts) {
    for item in opts.iter() {
      if let (Item::Claim([x, y], c), Some(ClaimKind::Taken)) = item {
        b[*y as usize][*x as usize] = Some(*c);
      }
    }
  }
  b
}

fn print_board<const M: usize, const N: usize>(b: [[Option<Color>; N]; M]) {
  for r in b {
    for c in r {
      print!("{}", c.map_or(' ', char::from));
    }
    println!();
  }
  println!();
}
