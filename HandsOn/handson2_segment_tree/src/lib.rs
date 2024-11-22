/// This code is an implementation of the Segment Tree providing a solution
/// to the two problems given for the 2nd HandsOn of Competitive Programming and Contest
/// at the University of Pisa (24/25)
///
/// [FIRST-PROBLEM] [STATUS = DONE]
/// You are given an array A[1,n] of n positive integers, each integer is at most n.
/// You have to build a data structure to answer two different types of queries:
/// - Update(i,j,T): ∀k in [1,n].A[k] = min(A[k], T)
/// - Max(i, j) that returns the largest value in A[i...j]
///
/// [SECOND-PROBLEM] [STATUS = on the high sea]
use std::cmp;

/// Represents a Node in a Segment Tree.
/// The main difference compared to a Node in a Binary Tree is that
/// we also specify the range of the Node, that is for which elements
/// the value of the key is indexed
struct MaxNode {
    key: usize,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
}

impl MaxNode {
    /// Base constructor
    fn new(key: usize, children: (Option<usize>, Option<usize>), range: (usize, usize)) -> Self {
        Self {
            key,
            children,
            range,
        }
    }
}

pub struct MaxSTree {
    nodes: Vec<MaxNode>,
    root: Option<usize>,
}

impl MaxSTree {
    /// Base Constructor
    /// Initializes an empty tree instance.
    fn empty_new() -> Self {
        Self {
            nodes: Vec::new(),
            root: None,
        }
    }

    /// Array Constructor
    /// Initializes a Max Segment Tree indexing the elements in `a`.
    /// #Errors
    /// If `a` is empty, then no tree will be constructed (`None` will be returned)
    pub fn new(a: &Vec<usize>) -> Option<Self> {
        // Check if `a` is empty
        if a.len() == 0 {
            eprintln!("Empty array passed, no tree will be constructed");
            return None;
        }
        let mut tree = MaxSTree::empty_new();

        tree.root = Some(tree.h_build(a, (0, a.len() - 1)));
        Some(tree)
    }

    /// Helper fn which recursively construct a Max Segment Tree.
    /// For each node `n[i,j]`, `n[i,j].key` = maximum value among
    /// the elements in the range `[i, j]`.
    /// # Returns
    /// The index of the created node in the Max Segment Tree.
    /// The first call will return the index of the root.
    fn h_build(&mut self, a: &Vec<usize>, range: (usize, usize)) -> usize {
        if range.0 == range.1 {
            // BASE CASE: LEAF
            self.nodes
                .push(MaxNode::new(a[range.0], (None, None), (range.0, range.0)));
        } else {
            // INDUCTIVE CASE: Internal Node
            let m = (range.0 + range.1) / 2;
            let lchd = self.h_build(&a, (range.0, m));
            let rchd = self.h_build(&a, (m + 1, range.1));
            let val = cmp::max(self.nodes[lchd].key, self.nodes[rchd].key);

            self.nodes
                .push(MaxNode::new(val, (Some(lchd), Some(rchd)), range));
        }
        self.nodes.len() - 1
    }

    /// A helper recursive fn that returns the maximum value within the range
    /// `m_range=[l, r]` as indexed by the tree.
    fn h_max(&self, q_range: (usize, usize), idx: usize) -> Option<usize> {
        let c_range = self.nodes[idx].range;

        // Base Case #1 - No Overlap
        if q_range.1 < c_range.0 || c_range.1 < q_range.0 {
            None
        }
        // Base Case #2 - Total Overlap
        else if q_range.0 <= c_range.0 && c_range.1 <= q_range.1 {
            Some(self.nodes[idx].key)
        }
        // Iterative Case - Partial Overlap
        else {
            let m = (c_range.0 + c_range.1) / 2;

            // Part of the solution in the LEFT SIDE
            let sol_l = if q_range.0 <= m {
                let idx = self.nodes[idx].children.0.unwrap();
                let r = cmp::min(q_range.1, m);
                self.h_max((q_range.0, r), idx)
            } else {
                None
            };

            // Part of the solution in the RIGHT SIDE
            let sol_r = if q_range.1 > m {
                let idx = self.nodes[idx].children.1.unwrap();
                let l = cmp::max(q_range.0, m);
                self.h_max((l, q_range.1), idx)
            } else {
                None
            };

            // Merge the two partial solutions
            cmp::max(sol_l, sol_r)
        }
    }

    /// Returns the maximum value within `query_range=[l, r]` as indexed by the tree.
    pub fn max(&self, q_range: (usize, usize)) -> Option<usize> {
        let idx = self.root.unwrap();

        // Check if the range is indexed by the tree
        if !(q_range.0 >= self.nodes[idx].range.0 && q_range.1 <= self.nodes[idx].range.1) {
            eprintln!("Range not indexed by the tree!");
            return None;
        }
        self.h_max(q_range, idx)
    }

    /// Helper recursive fn s.t given `u_range=[l,r]` and a value `t` then:
    /// ∀k in [l,r].A[k] = min(A[k], t)
    fn h_update(&mut self, u_range: (usize, usize), t: usize, idx: usize) -> usize {
        let c_range = self.nodes[idx].range;

        // Base Case #1 No Overlap
        if u_range.1 < c_range.0 || c_range.1 < u_range.0 {
            self.nodes[idx].key
        }
        // Base Case #2 Leaf Overlap
        else if c_range.0 == c_range.1 {
            self.nodes[idx].key = cmp::min(t, self.nodes[idx].key);
            self.nodes[idx].key
        }
        // Iterative Case Segment Overlap
        else {
            // Recurse on the LEFT SIDE
            let idx_l = self.nodes[idx].children.0.unwrap();
            let val_l = Some(self.h_update(u_range, t, idx_l));

            // Recurse on the RIGHT SIDE
            let idx_r = self.nodes[idx].children.1.unwrap();
            let val_r = Some(self.h_update(u_range, t, idx_r));

            // Merge partial solutions
            if let Some(val) = cmp::max(val_l, val_r) {
                self.nodes[idx].key = val;
            }
            self.nodes[idx].key
        }
    }

    /// Given `u_range=[l,r]` and a value `t` then:
    /// ∀k in [l,r].A[k] = min(A[k], t)
    pub fn update(&mut self, u_range: (usize, usize), t: usize) {
        // TODO Check if t = O(n)
        let idx = self.root.unwrap();
        self.h_update(u_range, t, idx);
    }
}

struct FreqNode {
    key: Vec<isize>,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
}

impl FreqNode {
    /// Base constructor
    /// TODO add better description
    fn new_leaf(a: &Vec<isize>, n: usize, i: usize) -> Self {
        let mut key = vec![0; n];
        let idx = usize::try_from(a[i]).unwrap();
        key[idx] = 1;
        Self {
            key,
            children: (None, None),
            range: (i, i),
        }
    }

    /// TODO add better description
    fn new_node(
        nodes: (&FreqNode, &FreqNode),
        indexes: (usize, usize),
        range: (usize, usize),
        n: usize,
    ) -> Self {
        // ∀i in [0, n-1].temp[i] = a[i] + b[i]
        let mut temp = vec![0; n];
        for i in 0..n {
            temp[i] = nodes.0.key[i] + nodes.1.key[i];
        }

        // Create and return self
        Self {
            key: temp,
            children: (Some(indexes.0), Some(indexes.1)),
            range: (range.0, range.1),
        }
    }

    /// Check if there exists a key whose content is `k`
    fn check_k(k: usize) -> Option<usize> {
        None
    }
}

pub struct FreqSTree {
    nodes: Vec<FreqNode>,
    root: Option<usize>,
}

impl FreqSTree {
    /// Base Constructor
    /// Initializes an empty tree instance.
    fn empty_new() -> Self {
        Self {
            nodes: Vec::new(),
            root: None,
        }
    }

    /// Array Constructor
    /// Initializes a Max Segment Tree indexing the elements in `a`.
    pub fn new(s: Vec<(usize, usize)>) -> Self {
        let mut tree = FreqSTree::empty_new();
        let a = FreqSTree::build_seg_array(s);
        tree.root = Some(tree.h_build(&a, 0, a.len() - 1));
        tree
    }

    /// Given a set of segments `s_set` = {s1; ...; sn}
    /// s.t each si = (l, r) where 0 <= l <= r <= n-1.
    /// The fn constructs an array `a[0, n-1]` s.t. each
    /// `a[i]` = # segments overlapping in position i
    fn build_seg_array(s_set: Vec<(usize, usize)>) -> Vec<isize> {
        let n = s_set.len();

        if n == 0 {
            return vec![];
        }

        let mut a = vec![0; n];
        for &s in s_set.iter() {
            a[s.0] += 1;
            if s.1 + 1 < n {
                a[s.1 + 1] -= 1;
            }
        }

        a.iter()
            .scan(0, |acc, &ai| {
                *acc += ai;
                Some(*acc)
            })
            .collect()
    }

    /// Constructs a Frequency Segment Tree from a given set of segments `s_set = {s1, ..., sn}`,
    /// where each segment `si` is defined as `(l, r)` with `0 <= l <= r <= n - 1`.
    /// Each node `n[i, j]` contains a table where each entry `e(key)` represents:
    /// `e(key) =` The number of positions within the range `[i, j]` that have exactly `key` overlapping segments.
    fn h_build(&mut self, a: &Vec<isize>, l: usize, r: usize) -> usize {
        // Base Case - Leaf
        if l == r {
            // Add Node here
            self.nodes.push(FreqNode::new_leaf(a, a.len(), l));
        }
        // Inductive Case - Internal Node
        else {
            let m = (l + r) / 2;
            let lchd = self.h_build(&a, l, m);
            let rchd = self.h_build(&a, m + 1, r);

            // Add Node here
            self.nodes.push(FreqNode::new_node(
                (&self.nodes[lchd], &self.nodes[rchd]),
                (lchd, rchd),
                (l, r),
                a.len(),
            ));
        }
        self.nodes.len() - 1
    }

    /// Given a `range=[i,j]` and a value `k` returns 1 if there exists a position `p` in `[i,j]`
    /// s.t. the #segments overlapping in p = k, 0 otherwise. Note that returning `p` is not
    /// requested, only to guarantee that is exists or not.
    fn h_is_there(&self, q_range: (usize, usize), idx: usize, k: usize) -> usize {
        let c_range = self.nodes[idx].range;

        // Base Case #1 - No Overlap
        if q_range.0 <= c_range.0 && c_range.1 <= q_range.1 {
            0
        }
        // Base Case #2 - Total Overlap
        else if q_range.0 <= c_range.0 && c_range.1 <= q_range.1 {
            // Return the Check in the node
            0
        }
        // Iterative Case - Partial Overlap
        else {
            let m = (c_range.0 + c_range.1) / 2;
            let sol_l = if q_range.0 <= m {
                if let Some(idx) = self.nodes[idx].children.0 {
                    // Return the Check function
                    0
                } else {
                    0
                }
            } else {
                0
            };
            if sol_l == 1 {
                return 1;
            }

            // Check for the right-side
            let sol_r = if q_range.1 > m {
                if let Some(idx) = self.nodes[idx].children.1 {
                    // Return the Check function
                    0
                } else {
                    0
                }
            } else {
                0
            };
            sol_r
        }
    }
}

/// A set of tests for constructing Max Segment Tree.
/// Each test construct a Max Segment Tree over 'a'.
/// Then visits the tree and checks if all nodes have
/// the same value as the correct tree.
/// For each test a visual representation of the tree is provided
#[cfg(test)]
mod build_fst_tests {
    use crate::FreqSTree;

    #[test]
    fn fst_1() {
        // [TEST - 1]
        // S = {(0, 0); (1, 3); (2, 3); (3, 5); (4, 4); (4, 5); (6, 6)}
        //                  (<1:3>; <2:2>; <3,2>)
        //                   /                  \
        //         (<1:2>; <2:1>; <3:1>)     (<1:1>; <2:1>; <3:1>)
        //           /        \                    /          \
        //       (<1;2>)    (<2:1>; <3:1>)    (<2:1>; <3:1>)   \
        //        /   \          /    \            /     \      \
        // A =   1     1         2     3          3      2       1
        // pos = 0     1         2     3          4      5       6
        let s = vec![(0, 0), (1, 3), (2, 3), (3, 5), (4, 4), (4, 5), (6, 6)];
        let tree = FreqSTree::new(s);
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, vec![0, 3, 2, 2, 0, 0, 0])
        }
    }
}

/// A set of tests for `build_seg_array` method.
/// Each test check if the created array is the one expected
/// For each test is provided a visual representation of the set
/// of segments and below the final A that will be constructed.
#[cfg(test)]
mod seg_array_tests {
    use crate::FreqSTree;

    #[test]
    fn sat_1() {
        // [TEST - 1]
        //       |---|
        //     |-| |
        // | |---| |-| |
        //
        // |-|-|-|-|-|-|->
        // 0 1 2 3 4 5 6
        // Solution = [1; 1; 2; 3; 3; 2; 1]
        let s = vec![(0, 0), (1, 3), (2, 3), (3, 5), (4, 4), (4, 5), (6, 6)];
        let a = FreqSTree::build_seg_array(s);
        assert_eq!(vec![1, 1, 2, 3, 3, 2, 1], a)
    }

    #[test]
    fn sat_2() {
        // [TEST - 2]
        //   |-|
        //   |
        // |-|
        // |-|-|->
        // 0 1 2
        // Solution = [1; 3; 1]
        let s = vec![(0, 1), (1, 1), (1, 2)];
        let a = FreqSTree::build_seg_array(s);
        assert_eq!(vec![1, 3, 1], a)
    }

    #[test]
    fn sat_3() {
        // [TEST - 3]

        // Solution = [1; 1; 1]
        let s = vec![(0, 0), (1, 1), (2, 2)];
        let a = FreqSTree::build_seg_array(s);
        assert_eq!(vec![1, 1, 1], a)
    }

    #[test]
    fn sat_4() {
        // [TEST - 4]

        // Solution = [] EMPTY
        let s = vec![];
        let a = FreqSTree::build_seg_array(s);
        let empty: Vec<isize> = Vec::new();
        assert_eq!(empty, a)
    }
}

/// A set of tests for 'update' function.
/// Each test check if the new tree follows the requested update
/// For each test is provided a visual representation of the tree.
#[cfg(test)]
mod update_query_tests {
    use crate::MaxSTree;

    #[test]
    fn ut_1() {
        // [TEST - 1] The constructed tree should be:
        // Query = Update((0,1), 1)
        //         2              1
        //       /   \    =>    /   \
        // A =  1     2        1     1
        // p =  0     1        0     1
        let a = vec![1, 2];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((0, 1), 1);
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 1);
        }
    }

    #[test]
    fn ut_2() {
        // [TEST - 2] The constructed tree should be:
        // Query = Update((2,2), 1)
        //           3                 3
        //         /   \            /    \
        //        3     \    =>    3      \
        //       / \     \        / \      \
        // A =  1  3      2      1  3       1
        // p =  0  1      2      0  1       2
        let a = vec![1, 3, 2];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((2, 2), 1);
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 3);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 3);
                assert_eq!(tree.nodes[r_idx].key, 1)
            }
        }
    }

    #[test]
    fn ut_3() {
        // [TEST - 3] The constructed tree should be:
        // Query = Update((1,2), 2)
        // Query = Update((1,2), 3) Doesn't do nothing!
        //            4                 4
        //          /   \             /    \
        //         4     3    =>     4      2
        //       /  \   /  \        / \    / \
        // A =  4   2   3   1      4   2  2   1
        // p =  0   1   2   3      0   1  2   3
        let a = vec![4, 2, 3, 1];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((1, 2), 2);
        tree.update((1, 2), 3);
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 4);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 4);
                assert_eq!(tree.nodes[r_idx].key, 2);
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 4);
                    assert_eq!(tree.nodes[r_idx].key, 2);
                }
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[r_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 2);
                    assert_eq!(tree.nodes[r_idx].key, 1)
                }
            }
        }
    }

    #[test]
    fn ut_4() {
        // [TEST - 4] The constructed tree should be:
        // Query = Update((0,3), 1)
        //               5                        5
        //            /     \                /        \
        //           4       \               1         \
        //          / \        5   =>      /   \        5
        //         4   \      / \         1     \      / \
        //       /  \   \    /   \      /   \    \    /   \
        // A =  4   2    3  1     5     1    1    1   1   5
        // p =  0   1   2   3     4
        let a = vec![4, 2, 3, 1, 5];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((0, 3), 1);
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 5);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 1);
                assert_eq!(tree.nodes[r_idx].key, 5);
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 1);
                    assert_eq!(tree.nodes[r_idx].key, 1);
                    if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                        assert_eq!(tree.nodes[l_idx].key, 1);
                        assert_eq!(tree.nodes[r_idx].key, 1);
                    }
                }
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[r_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 1);
                    assert_eq!(tree.nodes[r_idx].key, 5);
                }
            }
        }
    }

    #[test]
    fn ut_5() {
        // [TEST - 5] The constructed tree should be:
        // Query = Update((7,9), 10) Out of Range doesn't do nothing
        //                  6
        //            /          \
        //           6            5
        //          / \          /  \
        //         4   \         5   \
        //       /  \   \      /  \   \
        // A =  4   2    6    1    5   3
        // p =  0   1   2     3    4   5
        let a = vec![4, 2, 6, 1, 5, 3];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((7, 9), 10);
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 6);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 6);
                assert_eq!(tree.nodes[r_idx].key, 5);
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 4);
                    assert_eq!(tree.nodes[r_idx].key, 6);
                    if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                        assert_eq!(tree.nodes[l_idx].key, 4);
                        assert_eq!(tree.nodes[r_idx].key, 2);
                    }
                }
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[r_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 5);
                    assert_eq!(tree.nodes[r_idx].key, 3);
                    if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                        assert_eq!(tree.nodes[l_idx].key, 1);
                        assert_eq!(tree.nodes[r_idx].key, 5)
                    }
                }
            }
        }
    }
}

/// A set of tests for 'max' function.
/// Each test checks if the returned value is the max value
/// indexed by the tree in the requested range.
/// For each test a visual representation of the tree is provided.
/// ! <node> ! Specifies a node used to retrive the solution
#[cfg(test)]
mod max_query_tests {
    use crate::MaxSTree;

    #[test]
    fn mt_1() {
        // [TEST - 1] The constructed tree should be:
        //                  6
        //            /          \
        //           6           !3!
        //          / \          /  \
        //         6   \        2    \
        //       /  \   \      /  \   \
        // A =  6    5  !4!    2    1   3
        // p =  0   1    2     3    4   5
        // Query = max(2,5)
        // Solution = 4
        let a = vec![6, 5, 4, 2, 1, 3];
        let tree = MaxSTree::new(&a).unwrap();
        assert_eq!(tree.max((2, 5)), Some(4));
    }

    #[test]
    fn mt_2() {
        // [TEST -2] The constructed tree should be:
        //           3
        //          / \
        //         3   \
        //       /  \   \
        // A =  3    1   2
        // p =  0   1    2
        // Query = max(2,5)
        // Solution = None, the query goes out of range!
        let a = vec![3, 1, 2];
        let tree = MaxSTree::new(&a).unwrap();
        assert_eq!(tree.max((2, 5)), None);
    }

    #[test]
    fn mt_3() {
        // [TEST - 3] The constructed tree should be:
        //                      8
        //               /             \
        //              !4!               8
        //          /      \         /     \
        //         2        4        5       8
        //       /  \     /  \     /  \    /  \
        // A =  1    2    3   4    5   6   !7! 8
        // p =  0   1     2   3    4   5   6   7
        // Query = max(0,6)
        // Solution = 7
        let a = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let tree = MaxSTree::new(&a).unwrap();
        assert_eq!(tree.max((0, 6)), Some(7));
    }

    #[test]
    fn mt_4() {
        // [TEST - 4] The constructed tree should be:
        //                      8
        //               /             \
        //              !4!               8
        //          /      \         /     \
        //         2        4        5       8
        //       /  \     /  \     /  \    /  \
        // A =  1    2    3   4    5   6   !7! 8
        // p =  0   1     2   3    4   5   6   7
        // Query = max(0,0)
        // Solution = 1
        let a = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let tree = MaxSTree::new(&a).unwrap();
        assert_eq!(tree.max((0, 0)), Some(1));
    }

    #[test]
    fn mt_5() {
        // [TEST - 5] The constructed tree should be:
        //                5
        //           /         \
        //          !5!         \
        //         /  \          \
        //        5    \         2
        //       / \    \       /  \
        // A =  3   5    4     2    1
        // p =  0   1    2     3    4
        // Query = max(0,2)
        // Solution = 4
        let a = vec![3, 5, 4, 2, 1];
        let tree = MaxSTree::new(&a).unwrap();
        assert_eq!(tree.max((0, 2)), Some(5));
    }
}

/// A set of tests for constructing Max Segment Tree.
/// Each test construct a Max Segment Tree over 'a'.
/// Then visits the tree and checks if all nodes have
/// the same value as the correct tree.
/// For each test a visual representation of the tree is provided
#[cfg(test)]
mod build_max_segment_tree_tests {
    use crate::MaxSTree;

    #[test]
    fn mst_1() {
        // [TEST - 1] The constructed tree should be:
        //         2
        //       /   \
        // A =  1     2
        // p =  0     1
        let a = vec![1, 2];
        let tree = MaxSTree::new(&a).unwrap();
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 2)
        }
    }

    #[test]
    fn mst_2() {
        // [TEST - 2] The constructed tree should be:
        //           3
        //         /   \
        //        3     \
        //       / \     \
        // A =  1  3      2
        // p =  0  1      2
        let a = vec![1, 3, 2];
        let tree = MaxSTree::new(&a).unwrap();
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 3);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 3);
                assert_eq!(tree.nodes[r_idx].key, 2)
            }
        }
    }

    #[test]
    fn mst_3() {
        // [TEST - 3] The constructed tree should be:
        //            4
        //          /   \
        //         4     3
        //       /  \   /  \
        // A =  4   2   3   1
        // p =  0   1   2   3
        let a = vec![4, 2, 3, 1];
        let tree = MaxSTree::new(&a).unwrap();
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 4);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 4);
                assert_eq!(tree.nodes[r_idx].key, 3);
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 4);
                    assert_eq!(tree.nodes[r_idx].key, 2);
                }
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[r_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 3);
                    assert_eq!(tree.nodes[r_idx].key, 1);
                }
            }
        }
    }

    #[test]
    fn mst_4() {
        // [TEST - 4] The constructed tree should be:
        //               5
        //            /     \
        //           4       \
        //          / \        5
        //         4   \      / \
        //       /  \   \    /   \
        // A =  4   2    3  1     5
        // p =  0   1   2   3     4
        let a = vec![4, 2, 3, 1, 5];
        let tree = MaxSTree::new(&a).unwrap();
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 5);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 4);
                assert_eq!(tree.nodes[r_idx].key, 5);
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 4);
                    assert_eq!(tree.nodes[r_idx].key, 3);
                    if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                        assert_eq!(tree.nodes[l_idx].key, 4);
                        assert_eq!(tree.nodes[r_idx].key, 2);
                    }
                }
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[r_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 1);
                    assert_eq!(tree.nodes[r_idx].key, 5);
                }
            }
        }
    }

    #[test]
    fn mst_5() {
        // [TEST - 5] The constructed tree should be:
        //                  6
        //            /          \
        //           6            5
        //          / \          /  \
        //         4   \         5   \
        //       /  \   \      /  \   \
        // A =  4   2    6    1    5   3
        // p =  0   1   2     3    4   5
        let a = vec![4, 2, 6, 1, 5, 3];
        let tree = MaxSTree::new(&a).unwrap();
        if let Some(idx) = tree.root {
            assert_eq!(tree.nodes[idx].key, 6);
            if let (Some(l_idx), Some(r_idx)) = tree.nodes[idx].children {
                assert_eq!(tree.nodes[l_idx].key, 6);
                assert_eq!(tree.nodes[r_idx].key, 5);
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 4);
                    assert_eq!(tree.nodes[r_idx].key, 6);
                    if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                        assert_eq!(tree.nodes[l_idx].key, 4);
                        assert_eq!(tree.nodes[r_idx].key, 2);
                    }
                }
                if let (Some(l_idx), Some(r_idx)) = tree.nodes[r_idx].children {
                    assert_eq!(tree.nodes[l_idx].key, 5);
                    assert_eq!(tree.nodes[r_idx].key, 3);
                    if let (Some(l_idx), Some(r_idx)) = tree.nodes[l_idx].children {
                        assert_eq!(tree.nodes[l_idx].key, 1);
                        assert_eq!(tree.nodes[r_idx].key, 5)
                    }
                }
            }
        }
    }
}
