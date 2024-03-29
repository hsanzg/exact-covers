//! Finds all ways to put $2n$ numbers $\\{1,1,2,2,\dots,n,n\\}$ into $2n$ slots
//! so that there are exactly $i$ numbers between the two appearances of $i$,
//! for all $1\leq i\leq n$. This task is known as _Langford's problem_, and
//! its encoding as an exact cover problem is well explained in the book
//! [_The Art of Computer Programming_, Volume 4B, Part 2][taocp4b] (Addison-Wesley,
//! 2022) by D. E. Knuth. His approach can be summarized as follows:
//!
//! Regard the $n$ values of $i$ and the $2n$ slots as the items to be covered.
//! Then the legal options for permuting the first $n$ integers into a Langford
//! sequence are $`i\\;s_j\\;s_k'$ for $1\leq j<k\leq 2n$, $k=i+j+1$ and $1\leq i
//! \leq n$. In this way the distance between slots $s_j$ and $s_k$ for item $i$
//! is $k-j=i+j+1-j=i+1$, as desired.
//!
//! [taocp4b]: https://www-cs-faculty.stanford.edu/~knuth/taocp.html#vol4

use exact_covers::xc::ExactCovers;

// A Langford pair can exist only when $n$ is congruent to 0 or 3 modulo 4.
// This is because the two entries of an odd number must either both go in
// even or in odd positions, while the entries of an even number must fall
// in positions of different parity. There are $\floor{n/2}$ even numbers
// in $\\{1,\dots,n\\}$, so $n-\floor{n/2}=\ceil{n/2}$ positions of each
// parity remain available for the odd numbers. Since these come in pairs
// that occupy positions of the same parity, $\ceil{n/2}$ must be an even
// number. This happens only if $n\equiv 0$ or $n\equiv 3$ (modulo 4).
const N: usize = 8;

#[derive(Eq, PartialEq, Copy, Clone, Ord, PartialOrd)]
enum Item {
    Number(usize),
    Slot(usize),
}

fn main() {
    let numbers = (1..=N).map(Item::Number);
    let slots = (1..=2 * N).map(Item::Slot);
    let items: Vec<_> = numbers.chain(slots).collect();

    let mut solver = ExactCovers::new(&items, &[]);
    for i in 1..=N {
        // Optimization: half of the Langford pairs for a given value of $n$
        // are the reverses of the others. Reduce the search space by placing
        // the first 1 in position $1\leq s_j<n$.
        let first_slot_range = 1..if i == 1 { N } else { 2 * N - i };
        for j in first_slot_range {
            let k = i + j + 1;
            let option = [&Item::Number(i), &Item::Slot(j), &Item::Slot(k)];
            solver.add_option(option);
        }
    }

    let mut options = Vec::new();
    solver.solve(|mut solution| {
        assert_eq!(solution.option_count(), N);
        // Convert the set of options into the corresponding placement.
        let mut placement = [0usize; 2 * N];
        while solution.next(&mut options) {
            // Sort the items in `options` so we can perform pattern matching.
            // Note that `Item` derives `Ord`, so item variants are ordered by
            // their discriminants: numbers come before slots.
            options.sort();
            if let &[&Item::Number(i), &Item::Slot(j), &Item::Slot(k)] = &options[..] {
                placement[j - 1] = i;
                placement[k - 1] = i;
            } else {
                unreachable!("ordered option should match (number, slot, slot) pattern");
            }
        }
        // Print the found Langford sequence, and its reverse.
        println!("{:?}", placement);
        placement.reverse();
        println!("{:?}", placement);
    })
}
