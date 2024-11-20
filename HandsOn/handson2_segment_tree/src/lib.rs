/// This code is an implementation of the Segment Tree providing a solution
/// to the two problems given for the 2nd HandsOn of Competitive Programming and Contest
/// at the University of Pisa (24/25)
///
/// [FIRST-PROBLEM] [STATUS = Incomplete]
/// You are given an array A[1,n] of n positive integers, each integer is at most n.
/// You have to build a data structure to answer two different types of queries:
/// - Update(i,j,T): ∀k in [1,n].A[k] = min(A[k], T)
/// - Max(i, j) that returns the largest value in A[i...j]
///
/// [SECOND-PROBLEM] [STATUS = on the high sea]
use std::{cmp, io::stderr};

/// Represents a Node in a Segment Tree.
/// The main difference compared to a Node in a Binary Tree is that
/// we also specify the range of the Node, that is for which elements
/// the value of the key is indexed
pub struct STNode {
    key: usize,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
}

impl STNode {
    /// Base constructor
    fn new(key: usize, children: (Option<usize>, Option<usize>), range: (usize, usize)) -> Self {
        Self {
            key,
            children,
            range,
        }
    }
}

pub struct SegTree {
    nodes: Vec<STNode>,
    root_idx: Option<usize>,
}

impl SegTree {
    /// Base constructor
    pub fn empty_tree() -> Self {
        Self {
            nodes: Vec::new(),
            root_idx: None,
        }
    }

    /// Appends a node to the tree
    ///
    /// # Returns
    /// The index of the node in the vector abstracting the tree
    fn add_node(
        &mut self,
        val: usize,
        children: (Option<usize>, Option<usize>),
        range: (usize, usize),
    ) -> usize {
        self.nodes.push(STNode::new(val, children, range));
        self.nodes.len() - 1
    }

    /// Helper function which construct recursively a Max Segment Tree s.t.
    /// each node with range (i,j) has key = max among the [i,j] elements of
    /// `a` (the indexed array of the tree).
    ///
    /// # Returns
    /// Each call returns the index in `nodes` of the created node
    /// The first call will be the last to terminate and will return the index of the root.
    ///
    /// # Important
    /// This function is private, users should call max_build.

    fn helper_build_max_st(&mut self, a: &Vec<usize>, l: usize, r: usize) -> usize {
        if l == r {
            // BASE CASE: LEAF
            self.add_node(a[l], (None, None), (l, l))
        } else {
            // INDUCTIVE CASE: Internal Node
            let m = (l + r) / 2;
            let idx_lchd = self.helper_build_max_st(&a, l, m);
            let idx_rchd = self.helper_build_max_st(&a, m + 1, r);
            let val = cmp::max(self.nodes[idx_lchd].key, self.nodes[idx_rchd].key);
            self.add_node(val, (Some(idx_lchd), Some(idx_rchd)), (l, r))
        }
    }

    /// Dummy function which construct a Max Segment Tree indexed by the given array 'a'
    pub fn build_max_st(&mut self, a: &Vec<usize>) {
        match self.root_idx {
            None => self.root_idx = Some(self.helper_build_max_st(a, 0, a.len() - 1)),
            Some(_) => eprintln!("Cannot construct a Max Segment Tree over an not-empty tree"),
        }
    }

    /// Helper function which answer recursively a max(l, r) query for a the Max Segment Tree
    /// TODO Add Better Description
    fn helper_max(&self, m_range: (usize, usize), idx: usize) -> Option<usize> {
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
                    self.helper_max((max_l, r), idx)
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
                    self.helper_max((l, max_r), idx)
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

    /// max(l, r) returns the largest value in the subset [l...r] indexed by the Max Segment Tree
    /// TODO Add Better Description
    pub fn max(&self, query_range: (usize, usize)) -> Option<usize> {
        let (q_l, q_r) = query_range;
        if let Some(idx) = self.root_idx {
            // Checking if the query is in range
            // otherwise return None
            if q_l >= self.nodes[idx].range.0 && q_r <= self.nodes[idx].range.1 {
                self.helper_max(query_range, idx)
            } else {
                // Out of Range
                None
            }
        } else {
            None
        }
    }
    /// Recursive function which updates ∀k in [1,n].A[k] = min(A[k], T)
    /// TODO ADD BETTER COMMENT
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

    /// ∀k in [1,n].A[k] = min(A[k], T)
    /// TODO ADD BETTER COMMENT
    fn update(&mut self, u_range: (usize, usize), t: usize) {
        // TODO Check if t = O(n)
        if let Some(idx) = self.root_idx {
            self.helper_update(u_range, t, idx);
        }
    }
}

/// A set of tests for 'update' function.
/// Each test check if the new tree follows the requested update
/// For each test is provided a visual representation of the tree.
#[cfg(test)]
mod update_query_tests {
    use crate::SegTree;

    #[test]
    fn ut_1() {
        // [TEST - 1] The constructed tree should be:
        // Query = Update((0,1), 1)
        //         2              1
        //       /   \    =>    /   \
        // A =  1     2        1     1
        // p =  0     1        0     1
        let a = vec![1, 2];
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        tree.update((0, 1), 1);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        tree.update((2, 2), 1);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        tree.update((1, 2), 2);
        tree.update((1, 2), 3);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        tree.update((0, 3), 1);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        tree.update((7, 9), 10);
        if let Some(idx) = tree.root_idx {
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
    use crate::SegTree;

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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
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
    use crate::SegTree;

    #[test]
    fn mst_1() {
        // [TEST - 1] The constructed tree should be:
        //         2
        //       /   \
        // A =  1     2
        // p =  0     1
        let a = vec![1, 2];
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        if let Some(idx) = tree.root_idx {
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
        let mut tree = SegTree::empty_tree();
        tree.build_max_st(&a);
        if let Some(idx) = tree.root_idx {
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
