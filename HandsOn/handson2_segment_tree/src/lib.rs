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

/// Helper fn which recursively construct a Max Segment Tree.
/// For each node `n[i,j]`, `n[i,j].key` = maximum value among
/// the elements in the range `[i, j]`.
/// # Returns
/// The index of the created node in the Max Segment Tree.
/// The first call will return the index of the root.

fn h_build(nodes: &mut Vec<MaxNode>, a: &Vec<usize>, l: usize, r: usize) -> usize {
    if l == r {
        // BASE CASE: LEAF
        nodes.push(MaxNode::new(a[l], (None, None), (l, l)));
    } else {
        // INDUCTIVE CASE: Internal Node
        let m = (l + r) / 2;
        let lchd = h_build(nodes, &a, l, m);
        let rchd = h_build(nodes, &a, m + 1, r);
        let val = cmp::max(nodes[lchd].key, nodes[rchd].key);

        nodes.push(MaxNode::new(val, (Some(lchd), Some(rchd)), (l, r)));
    }
    nodes.len() - 1
}

/// Represents a Node in a Segment Tree.
/// The main difference compared to a Node in a Binary Tree is that
/// we also specify the range of the Node, that is for which elements
/// the value of the key is indexed
pub struct MaxNode {
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
    /// Note that this tree cannot be used as it is.
    /// Users must call `build` to construct the Max Segment Tree.
    pub fn new(a: &Vec<usize>) -> Self {
        let mut temp: Vec<MaxNode> = Vec::new();
        let root = h_build(&mut temp, a, 0, a.len() - 1);

        Self {
            nodes: temp,
            root: Some(root),
        }
    }

    /// A helper recursive fn that returns the maximum value within the range
    /// `m_range=[l, r]` as indexed by the tree.
    fn h_max(&self, m_range: (usize, usize), idx: usize) -> Option<usize> {
        let (curr_l, curr_r) = self.nodes[idx].range;
        let (max_l, max_r) = m_range;

        // Base Case #1 - No Overlap
        if max_r < curr_l || curr_r < max_l {
            None
        }
        // Base Case #2 - Total Overlap
        else if max_l <= curr_l && curr_r <= max_r {
            Some(self.nodes[idx].key)
        }
        // Iterative Case - Partial Overlap
        else {
            let m = (curr_l + curr_r) / 2;
            // Part of the solution in the LEFT SIDE
            let sol_l = if max_l <= m {
                if let Some(idx) = self.nodes[idx].children.0 {
                    let r = cmp::min(max_r, m);
                    self.h_max((max_l, r), idx)
                } else {
                    None
                }
            } else {
                None
            };

            // Part of the solution in the RIGHT SIDE
            let sol_r = if max_r > m {
                if let Some(idx) = self.nodes[idx].children.1 {
                    let l = cmp::max(max_l, m);
                    self.h_max((l, max_r), idx)
                } else {
                    None
                }
            } else {
                None
            };

            // Return the solution
            cmp::max(sol_l, sol_r)
        }
    }

    /// Returns the maximum value within `query_range=[l, r]` as indexed by the tree.
    pub fn max(&self, query_range: (usize, usize)) -> Option<usize> {
        let (q_l, q_r) = query_range;
        if let Some(idx) = self.root {
            // Checking if the query is in range
            // otherwise return None
            if q_l >= self.nodes[idx].range.0 && q_r <= self.nodes[idx].range.1 {
                self.h_max(query_range, idx)
            } else {
                // Out of Range
                None
            }
        } else {
            None
        }
    }

    /// Helper recursive fn s.t given `u_range=[l,r]` and a value `t` then:
    /// ∀k in [l,r].A[k] = min(A[k], t)
    fn helper_update(&mut self, u_range: (usize, usize), t: usize, idx: usize) -> usize {
        let (u_l, u_r) = u_range;
        let (curr_l, curr_r) = self.nodes[idx].range;

        // Base Case #1 No Overlap
        if u_r < curr_l || curr_r < u_l {
            self.nodes[idx].key
        }
        // Base Case #2 Leaf Overlap
        else if curr_l == curr_r {
            self.nodes[idx].key = cmp::min(t, self.nodes[idx].key);
            self.nodes[idx].key
        }
        // Iterative Case Segment Overlap
        else {
            let val_l = if let Some(idx) = self.nodes[idx].children.0 {
                Some(self.helper_update(u_range, t, idx))
            } else {
                None
            };

            let val_r = if let Some(idx) = self.nodes[idx].children.1 {
                Some(self.helper_update(u_range, t, idx))
            } else {
                None
            };

            if let Some(val) = cmp::max(val_l, val_r) {
                self.nodes[idx].key = val;
            }
            self.nodes[idx].key
        }
    }

    /// Given `u_range=[l,r]` and a value `t` then:
    /// ∀k in [l,r].A[k] = min(A[k], t)
    fn update(&mut self, u_range: (usize, usize), t: usize) {
        // TODO Check if t = O(n)
        if let Some(idx) = self.root {
            self.helper_update(u_range, t, idx);
        }
    }
}

pub struct FreqNode {
    key: Vec<usize>,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
}

impl FreqNode {
    /// Base constructor
    /// TODO add better description
    pub fn new(n: usize, i: usize) -> Self {
        let mut key = vec![0; n];
        key[i] = 1;
        Self {
            key,
            children: (None, None),
            range: (i, i),
        }
    }
}

pub struct FreqSTree {
    nodes: Vec<FreqNode>,
    root: Option<usize>,
}

impl FreqSTree {
    /// Given a set of segments `s_set` = {s1; ...; sn}
    /// s.t each si = (l, r) where 0 <= l <= r <= n-1.
    /// The fn constructs an array `a[0, n-1]` s.t. each
    /// `a[i]` = # segments overlapping in position i
    fn build_seg_array(s_set: Vec<(usize, usize)>) -> Vec<isize> {
        let n = s_set.len();
        let a: &mut Vec<isize> = &mut vec![0; n];
        for &s in s_set.iter() {
            a[s.0] += 1;
            if s.1 + 1 < n {
                a[s.1 + 1] -= 1;
            }
        }
        for i in 1..n {
            a[i] += a[i - 1];
        }
        a.clone() //TODO Find a better version
    }

    /// Constructs a Frequency Segment Tree from a given set of segments `s_set = {s1, ..., sn}`,
    /// where each segment `si` is defined as `(l, r)` with `0 <= l <= r <= n - 1`.
    /// Each node `n[i, j]` contains a table where each entry `e(key)` represents:
    /// `e(key) =` The number of positions within the range `[i, j]` that have exactly `key` overlapping segments.
    fn h_build(&mut self, a: &Vec<usize>, l: usize, r: usize) -> usize {
        // Base Case - Leaf
        if l == r {
            // Add Node here
            0
        }
        // Inductive Case - Internal Node
        else {
            let m = (l + r) / 2;
            let lchd = self.h_build(&a, l, m);
            let rchd = self.h_build(&a, m + 1, r);
            // Call Merge Funciton
            // Add Node here
            0
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
        let mut tree = MaxSTree::new(&a);
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
        let mut tree = MaxSTree::new(&a);
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
        let mut tree = MaxSTree::new(&a);
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
        let mut tree = MaxSTree::new(&a);
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
        let mut tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
        assert_eq!(tree.max((0, 2)), Some(5));
    }
}

/// A set of tests for 'max_build' function.
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
        let tree = MaxSTree::new(&a);
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
