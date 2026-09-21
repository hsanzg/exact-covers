#[path = "common/polycubes.rs"]
mod polycubes;

use exact_covers::{DlSolver, Solution, Solver};
use polycubes::{Polycube, Pos};
use std::collections::HashSet;
use std::ops::ControlFlow;
use std::{array, iter};

pub fn neighbors<const N: usize>(p: &Pos<N>) -> Vec<Pos<N>> {
  let mut ns = Vec::with_capacity(3usize.pow(N as u32) - 1);
  let mut d = [-1i8; N];
  loop {
    if d.iter().any(|&d| d != 0) {
      ns.push(array::from_fn(|i| p[i] + d[i]));
    }
    // Advance to the next neighbor.
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
  ns
}

fn touching<const N: usize>(pc: &Polycube<N>) -> HashSet<Pos<N>> {
  let mut b = HashSet::new();
  for c in pc.cubies() {
    b.extend(neighbors(c));
  }
  for c in pc.cubies() {
    b.remove(c);
  }
  b
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Color {
  Orange,
  Pink,
  Blue,
}

impl Color {
  pub fn all() -> &'static [Self] {
    &[Self::Orange, Self::Pink, Self::Blue]
  }

  pub fn ansi_esc(self) -> &'static str {
    match self {
      Self::Orange => "\x1b[0;33m",
      Self::Pink => "\x1b[0;31m",
      Self::Blue => "\x1b[0;36m",
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Item {
  Occupy(Pos<2>),       // primary.
  Claim(Pos<2>, Color), // secondary.
  Empty,                // secondary.
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum ClaimKind {
  Taken,
  Touching,
}

pub fn main() {
  const M: u8 = 8;
  const N: u8 = 8;

  let cells = (0..M as i8).flat_map(|y| (0..N as i8).map(move |x| [x, y]));
  let occup: Vec<_> = cells.clone().map(Item::Occupy).collect();
  let touch = cells.flat_map(|p| Color::all().iter().map(move |&c| Item::Claim(p, c)));
  let sec: Vec<_> = touch.chain(iter::once(Item::Empty)).collect();

  let bent = Polycube::from([[0, 0], [0, 1], [1, 0]]);
  let placements = bent.base_placements();

  for vy in 1..=M.div_ceil(2) {
    for vx in 1..=vy.min(N.div_ceil(2)) {
      if M == N && vx == 1 && vy == 1 {
        continue;
      }

      let (vx, vy) = (vx.cast_signed(), vy.cast_signed());
      // Break symmetry by forcing the diagonally-touching trominoes
      // to go in the upper-right direction. This is equivalent to
      // forcing the orientation of the piece occupying cell $(0,0)$
      // to three of four positions. // todo: Is it?
      // todo: Apply these only when $m=n$.
      let allowed_diag = [[vx - 1, vy - 1], [vx, vy]]; // [[vx - 1, vy], [vx, vy - 1]];

      let mut solver = DlSolver::new(&occup, &sec);
      let (mut occup, mut claims) = (Vec::new(), Vec::new());
      for shape in &placements {
        for y0 in 0..M as i8 - 1 {
          for x0 in 0..N as i8 - 1 {
            let pc = shape.transform(|[x, y]| [x + x0, y + y0]);

            for &c in Color::all() {
              occup.clear();
              claims.clear();

              occup.extend(pc.cubies().iter().copied().map(Item::Occupy));
              assert_eq!(occup.len(), 3);

              claims.extend(
                pc.cubies()
                  .iter()
                  .copied()
                  .map(|p| (Item::Claim(p, c), Some(ClaimKind::Taken))),
              );
              assert_eq!(claims.len(), 3);

              claims.extend(
                touching(&pc)
                  .into_iter()
                  .filter(|&[x, y]| 0 <= x && x < N as i8 && 0 <= y && y < M as i8)
                  .filter(|p| !allowed_diag.contains(p))
                  .map(|p| (Item::Claim(p, c), Some(ClaimKind::Touching))),
              );
              assert!(claims.len() <= 3 + 12);

              solver.add_option(&occup, &claims);

              // Break symmetry by forcing the color of the tromino
              // occupying cell $0,0$.
              if x0 == 0 && y0 == 0 {
                break;
              }
            }
          }
        }
      }

      // Add option to cover empty cells.
      for y in 0..M as i8 {
        for x in 0..N as i8 {
          solver.add_option(&[Item::Occupy([x, y])], &[(Item::Empty, None)])
        }
      }

      println!("solving for vertex {vx}, {vy}");
      let mut opts = Vec::new();
      let mut c = 0;
      solver.solve(|mut sol| {
        print_sol::<_, { M as usize }, { N as usize }>(&mut sol, &mut opts);
        c += 1;
        ControlFlow::Continue(())
      });
      println!("found {c} sols!");
    }
  }
}

fn print_sol<'i, S, const M: usize, const N: usize>(
  sol: &mut Solution<'_, 'i, Item, ClaimKind, S>,
  mut opts: &mut Vec<(&'i Item, Option<ClaimKind>)>,
) where
  S: Solver<'i, Item, ClaimKind>,
{
  let mut board: [[Color; N]; M] = array::repeat(array::repeat(Color::Orange));
  while sol.next(&mut opts) {
    for item in opts.iter() {
      if let (Item::Claim([x, y], c), Some(ClaimKind::Taken)) = item {
        board[*y as usize][*x as usize] = *c;
      }
    }
  }
  for row in board {
    for c in row {
      print!(
        "{}",
        match c {
          Color::Orange => "o",
          Color::Pink => "p",
          Color::Blue => "b",
        }
      );
      // print!("{}█", c.ansi_esc());
    }
    println!();
  }
  println!();
  // println!("\x1b[0m");
}
