use priority_queue::PriorityQueue;
use rand::seq::SliceRandom;
use rand::Rng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::{
    collections::{BTreeSet, HashMap},
    fmt::{Debug, Display},
    iter::Sum,
    ops::Add,
    time::Instant,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Card {
    kind: u8,
}

impl Display for Card {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if (self.kind as char).is_ascii_alphanumeric() {
            write!(f, "{}", self.kind as char)
        } else {
            write!(f, "{}", self.kind)
        }
    }
}

impl Debug for Card {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.kind)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Saved {
    Card(Card),
    Locked,
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum Stack {
    Stack(CardStack),
    Locked,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct CardStack {
    cards: Vec<Card>,
}

impl CardStack {
    fn top(&self) -> Option<Card> {
        self.cards.last().copied()
    }

    /// Maximum number of cards that can be moved from this stack
    fn max_num_cards(&self) -> usize {
        let Some(card) = self.cards.last() else {
            return 0;
        };

        let mut n = 1;

        for c in self.cards.iter().rev().skip(1) {
            if c != card {
                break;
            }
            n += 1;
        }

        n
    }
}

impl Stack {
    fn cards(&self) -> Option<&CardStack> {
        match self {
            Stack::Stack(cards) => Some(cards),
            Stack::Locked => None,
        }
    }

    fn cards_mut(&mut self) -> Option<&mut CardStack> {
        match self {
            Stack::Stack(cards) => Some(cards),
            Stack::Locked => None,
        }
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct State {
    stacks: Vec<Stack>,
    saved: Vec<Option<Saved>>,
}

impl Debug for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for s in self.saved.iter() {
            match s {
                Some(Saved::Locked) => write!(f, "L")?,
                Some(Saved::Card(c)) => write!(f, "{}", c)?,
                None => write!(f, "F")?,
            }
        }
        writeln!(f, "")?;
        writeln!(f, "")?;

        let max_height = self
            .stacks
            .iter()
            .map(|x| x.cards().map(|x| x.cards.len()).unwrap_or(0))
            .max()
            .unwrap_or(0)
            .max(1);

        for height in 0..max_height {
            for stack in self.stacks.iter() {
                let Some(card_stack) = stack.cards() else {
                    if height == 0 {
                        write!(f, "L")?;
                    } else {
                        write!(f, " ")?;
                    }
                    continue;
                };
                if let Some(card) = card_stack.cards.get(height) {
                    write!(f, "{}", card)?;
                } else {
                    if height == 0 {
                        write!(f, "F")?;
                    } else {
                        write!(f, " ")?;
                    }
                }
            }
            writeln!(f, "")?;
        }

        Ok(())
    }
}

impl State {
    fn new(stacks: usize, saved: usize) -> Self {
        State {
            stacks: vec![Stack::Stack(CardStack { cards: vec![] }); stacks],
            saved: vec![None; saved],
        }
    }

    fn parse(stacks: usize, saved: usize, s: &str) -> Self {
        let mut st = State::new(stacks, saved);

        for (stack, l) in s.trim().lines().enumerate() {
            for (i, c) in l.chars().enumerate() {
                if c == 'L' {
                    st.stacks[stack] = Stack::Locked;
                    assert_eq!(i, 0);
                } else {
                    st.stacks[stack]
                        .cards_mut()
                        .unwrap()
                        .cards
                        .push(Card { kind: c as u8 });
                }
            }
        }

        st
    }

    fn rand(stacks: usize, saved: usize) -> Self {
        let mut state = Self::new(stacks, saved);

        let mut rng = rand::thread_rng();

        let mut cards = vec![];
        for card_id in 0..10 {
            for _ in 0..4 {
                cards.push(card_id);
            }
        }
        (&mut cards[..]).shuffle(&mut rng);
        let mut to = 0;
        for card in cards {
            state.stacks[to]
                .cards_mut()
                .unwrap()
                .cards
                .push(Card { kind: card });
            to += 1;
            to %= state.stacks.len();
        }

        state
    }
    fn moves(&self) -> Vec<Move> {
        let mut v = Vec::new();

        for (from, from_stack) in self.stacks.iter().enumerate() {
            let Some(from_card_stack) = from_stack.cards() else {
                continue;
            };
            let Some(from_card) = from_card_stack.top() else {
                continue;
            };
            let max_n = from_card_stack.max_num_cards();

            for (to, to_stack) in self.stacks.iter().enumerate() {
                if from == to {
                    continue;
                }
                let Some(to_card_stack) = to_stack.cards() else {
                    continue;
                };
                let to_card = to_card_stack.top();
                match (from_card, to_card) {
                    (_, None) => {
                        for i in (1..=max_n).rev() {
                            v.push(Move::StackToStack { from, to, count: i });
                        }
                    }
                    (x, Some(y)) if x == y => {
                        for i in (1..=max_n).rev() {
                            v.push(Move::StackToStack { from, to, count: i });
                        }
                    }
                    _ => {}
                }
            }

            for to in 0..self.saved.len() {
                if self.saved[to].is_none() {
                    v.push(Move::StackToSaved { from, to, count: 1 });
                    if max_n == 4 {
                        v.push(Move::StackToSaved { from, to, count: 4 });
                    }
                    break;
                }
            }
        }

        for from in 0..self.saved.len() {
            let Some(Saved::Card(from_card)) = self.saved[from] else {
                continue;
            };
            for (to, to_stack) in self.stacks.iter().enumerate() {
                let Some(to_card_stack) = to_stack.cards() else {
                    continue;
                };
                let to_card = to_card_stack.top();
                if to_card.is_none() || to_card.unwrap() == from_card {
                    v.push(Move::SavedToStack { from, to });
                }
            }
        }

        v
    }

    fn lock_stack_if_lockable(&mut self, id: usize) {
        let stack = self.stacks[id].cards_mut().unwrap();
        if stack.cards.len() == 4 {
            let c = stack.cards[0];
            if stack.cards.iter().all(|x| *x == c) {
                self.stacks[id] = Stack::Locked;
                if self.saved.len() < 4 {
                    self.saved.push(None);
                }
            }
        }
    }

    fn play(&mut self, m: Move) {
        match m {
            Move::StackToStack { from, to, count } => {
                debug_assert!(count > 0);
                let from_card_stack = self.stacks[from].cards_mut().unwrap();
                let card = from_card_stack.cards.pop().unwrap();
                for _ in 1..count {
                    assert_eq!(from_card_stack.cards.pop().unwrap(), card);
                }
                let to_card_stack = self.stacks[to].cards_mut().unwrap();
                debug_assert!(
                    to_card_stack.top().is_none() || to_card_stack.top().unwrap() == card
                );
                for _ in 0..count {
                    to_card_stack.cards.push(card);
                }

                self.lock_stack_if_lockable(to);
                self.lock_stack_if_lockable(from);
            }
            Move::StackToSaved { from, to, count } => {
                debug_assert!(count > 0 && (count == 1 || count == 4));
                let from_card_stack = self.stacks[from].cards_mut().unwrap();
                let card = from_card_stack.cards.pop().unwrap();
                for _ in 1..count {
                    assert_eq!(from_card_stack.cards.pop().unwrap(), card);
                }
                let to_card_stack = &mut self.saved[to];
                if to_card_stack.is_some() {
                    panic!("Saved stack already occupied");
                }
                if count == 1 {
                    *to_card_stack = Some(Saved::Card(card));
                } else if count == 4 {
                    *to_card_stack = Some(Saved::Locked);
                }
                self.lock_stack_if_lockable(from);
            }
            Move::SavedToStack { from, to } => {
                let from_card_stack = &mut self.saved[from];
                let card = match from_card_stack {
                    Some(Saved::Card(c)) => *c,
                    Some(Saved::Locked) => {
                        panic!("Moving a card from a locked saved pile");
                    }
                    None => {
                        panic!("Moving a card from an empty saved pile");
                    }
                };
                let to_card_stack = self.stacks[to].cards_mut().unwrap();
                debug_assert!(
                    to_card_stack.top().is_none() || to_card_stack.top().unwrap() == card
                );
                to_card_stack.cards.push(card);
                *from_card_stack = None;
                self.lock_stack_if_lockable(to);
            }
        }
    }

    fn solve(&self) -> Vec<Move> {
        // let start = Instant::now();
        let mut visited: HashMap<State, Option<(State, Move)>> = HashMap::new();

        let mut max_num_locked = 0;
        let mut frontier = PriorityQueue::new();
        let ci = |e: &QueueEntry| -(e.state.groups() as i64 + e.moves as i64);
        let init = QueueEntry {
            state: self.clone(),
            moves: 0,
            from: None,
        };
        let v = ci(&init);
        frontier.push(init, v);

        while let Some((s, _p)) = frontier.pop() {
            if visited.contains_key(&s.state) {
                continue;
            }
            visited.insert(s.state.clone(), s.from);
            let new_locked = s.state.num_locked();
            if new_locked > max_num_locked {
                max_num_locked = new_locked;
                // println!("New max locked: {new_locked}");
            }
            if new_locked == 10 {
                let mut path = vec![];
                let mut cur_state = s.state;
                loop {
                    if let Some(Some((prev, m))) = &visited.get(&cur_state) {
                        cur_state = prev.clone();
                        path.push(*m);
                    } else {
                        path.reverse();
                        // let duration = start.elapsed();
                        // println!(
                        //     "Cleaning up {} visited items and {} frontier items. Took {duration:?} and visited {:.02} states/second. Final path length is {}.",
                        //     visited.len(),
                        //     frontier.len(),
                        //     visited.len() as f64 / duration.as_secs_f64(),
                        //     path.len(),
                        // );
                        return path;
                    }
                }
            }
            let ms = s.state.moves();
            for m in ms {
                let mut next_state = s.state.clone();
                next_state.play(m);
                if !visited.contains_key(&next_state) {
                    let e = QueueEntry {
                        state: next_state,
                        moves: s.moves + 1,
                        from: Some((s.state.clone(), m)),
                    };
                    let v = ci(&e);
                    frontier.push(e, v);
                }
            }
        }

        vec![]
    }

    fn num_locked(&self) -> usize {
        let mut locked = 0;
        for saved in self.saved.iter() {
            if let Some(Saved::Locked) = saved {
                locked += 1;
            }
        }
        for stack in self.stacks.iter() {
            if stack == &Stack::Locked {
                locked += 1;
            }
        }
        locked
    }

    fn groups(&self) -> usize {
        let mut n_groups = 0;
        let mut locked = 0;
        let mut distinct_grounded = [false; 256];

        for stack in self.stacks.iter() {
            let mut last = None;
            if let Some(cards) = stack.cards() {
                for (i, card) in cards.cards.iter().enumerate() {
                    if i == 0 {
                        distinct_grounded[card.kind as usize] = true;
                    }
                    if let Some(last_card) = last {
                        if *card != last_card {
                            n_groups += 1;
                            last = Some(*card);
                        }
                    } else {
                        n_groups += 1;
                        last = Some(*card);
                    }
                }
            } else {
                locked += 1;
            }
        }

        for saved in self.saved.iter() {
            if let Some(saved) = saved {
                if let Saved::Card(card) = saved {
                    n_groups += 1;
                    distinct_grounded[card.kind as usize] = true;
                } else {
                    locked += 1;
                }
            }
        }

        let l2 = self.num_locked();
        debug_assert_eq!(l2, locked);
        let remaining = 10 - l2;
        let moves_to_ground =
            remaining - distinct_grounded.iter().map(|x| *x as usize).sum::<usize>();
        n_groups + moves_to_ground - remaining
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
struct QueueEntry {
    state: State,
    moves: usize,
    from: Option<(State, Move)>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
enum Move {
    StackToStack {
        from: usize,
        to: usize,
        count: usize,
    },
    StackToSaved {
        from: usize,
        to: usize,
        count: usize,
    },
    SavedToStack {
        from: usize,
        to: usize,
    },
}

fn main() {
    //     let mut state = State::parse(
    //         8,
    //         2,
    //         r"
    // L
    // tlhjl
    // ewwww
    // thjtl
    // jj
    // deyt
    // yhydy
    // leedd
    //     ",
    //     );

    //     state.saved[0] = Some(Saved::Card(Card { kind: b'h' }));
    //     state.saved[1] = Some(Saved::Locked);
    // state.saved[2] = Some(Saved::Card(Card { kind: b'e' }));
    // state.saved[3] = Some(Saved::Card(Card { kind: b'r' }));

    struct Stats {
        n: usize,
        solvable: usize,
        path_lengths: usize,
    }

    impl Add for Stats {
        type Output = Stats;

        fn add(self, rhs: Self) -> Self::Output {
            Stats {
                n: self.n + rhs.n,
                solvable: self.solvable + rhs.solvable,
                path_lengths: self.path_lengths + rhs.path_lengths,
            }
        }
    }
    impl Sum for Stats {
        fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.reduce(|a, x| a + x).unwrap_or(Stats {
                n: 0,
                solvable: 0,
                path_lengths: 0,
            })
        }
    }

    let stats: Vec<Stats> = (0..10000)
        .into_par_iter()
        .map(|_| {
            let state = State::rand(8, 1);
            // println!("{state}");
            let path = state.solve();
            // if path.len() > 0 {
            //     solvable += 1;
            // }
            // n += 1;
            // for m in path.iter() {
            //     println!("{m:?}");
            //     state.play(m.clone());
            //     println!("{state}");
            // }
            // println!("Path length: {}", path.len());
            Stats {
                n: 1,
                solvable: if path.len() > 0 { 1 } else { 0 },
                path_lengths: path.len(),
            }
            // path_lengths += path.len();
            // println!(
            //     "Solvable: {solvable}/{n} = {:.02}% with average path length of {:.02}",
            //     solvable as f64 / n as f64 * 100.0,
            //     path_lengths as f64 / n as f64,
            // );
        })
        .collect();

    let mut path_lengths: Vec<usize> = stats
        .iter()
        .map(|x| x.path_lengths)
        .filter(|x| *x != 0)
        .collect();
    path_lengths.sort_unstable();
    println!("Max path length: {}", path_lengths.last().unwrap());
    println!("Min path length: {}", path_lengths.first().unwrap());
    println!(
        "Median path length: {}",
        path_lengths[path_lengths.len() / 2]
    );

    let stats: Stats = stats.into_iter().sum();

    println!(
        "Solvable: {}/{} = {:.02}% with average path length of {:.02}",
        stats.solvable,
        stats.n,
        stats.solvable as f64 / stats.n as f64 * 100.0,
        stats.path_lengths as f64 / stats.solvable as f64,
    );
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_card_stack() {
        let stack = CardStack { cards: vec![] };
        assert_eq!(stack.max_num_cards(), 0);
        let stack = CardStack {
            cards: vec![Card { kind: 0 }],
        };
        assert_eq!(stack.max_num_cards(), 1);
        let stack = CardStack {
            cards: vec![Card { kind: 0 }, Card { kind: 1 }],
        };
        assert_eq!(stack.max_num_cards(), 1);
        let stack = CardStack {
            cards: vec![Card { kind: 0 }, Card { kind: 0 }],
        };
        assert_eq!(stack.max_num_cards(), 2);
        let stack = CardStack {
            cards: vec![Card { kind: 0 }, Card { kind: 0 }, Card { kind: 0 }],
        };
        assert_eq!(stack.max_num_cards(), 3);
        let stack = CardStack {
            cards: vec![Card { kind: 1 }, Card { kind: 0 }, Card { kind: 0 }],
        };
        assert_eq!(stack.max_num_cards(), 2);
        let stack = CardStack {
            cards: vec![
                Card { kind: 0 },
                Card { kind: 0 },
                Card { kind: 0 },
                Card { kind: 0 },
            ],
        };
        assert_eq!(stack.max_num_cards(), 4);
        let stack = CardStack {
            cards: vec![
                Card { kind: 1 },
                Card { kind: 0 },
                Card { kind: 0 },
                Card { kind: 0 },
                Card { kind: 0 },
            ],
        };
        assert_eq!(stack.max_num_cards(), 4);
    }
}
