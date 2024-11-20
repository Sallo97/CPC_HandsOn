/// This code is an implementation of the Segment Tree providing a solution
/// to the two problems given for the 2nd HandsOn of Competitive Programming and Contest
/// at the University of Pisa (24/25)
///
/// [FIRST-PROBLEM] [STATUS = Incomplete]
/// You are given an array A[1,n] of n positive integers, each integer is at most n.
/// You have to build a data structure to answer two different types of queries:
/// - Update(i,j,T): ∀ k in [1,n].A[k] = min(A[k], T)
/// - Max(i, j) that returns the largest value in A[i...j]
///
/// [SECOND-PROBLEM] [STATUS = on the high sea]
use std::cmp;

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

    /// Helper function which construct recurively a Max Segment Tree s.t.
    /// each node with range (i,j) has key = max among the [i,j] elements of
    /// `a` (the indexed array of the tree).
    ///
    /// # Returns
    /// Each call returns the index in `nodes` of the created node
    /// The first call will be the last to terminate and will return the index of the root.
    ///
    /// # Important
    /// This function is private, users should call max_build.

    fn helper_max_build(&mut self, a: &Vec<usize>, l: usize, r: usize) -> usize {
        if l == r {
            // BASE CASE: LEAF
            self.add_node(a[l], (None, None), (l, l))
        } else {
            // INDUCTIVE CASE: Internal Node
            let m = (l + r) / 2;
            let idx_lchd = self.helper_max_build(&a, l, m);
            let idx_rchd = self.helper_max_build(&a, m + 1, r);
            let val = cmp::max(self.nodes[idx_lchd].key, self.nodes[idx_rchd].key);
            self.add_node(val, (Some(idx_lchd), Some(idx_rchd)), (l, r))
        }
    }

    /// Dummy function which construct a Max Segment Tree indexed by given array 'a'
    pub fn max_build(&mut self, a: &Vec<usize>) {
        match self.root_idx {
            None => self.root_idx = Some(self.helper_max_build(a, 0, a.len() - 1)),
            Some(_) => eprintln!("Cannot construct a Max Segment Tree over an not-empty tree"),
        }
    }
}

/// A set of tests for 'max_build' function.
/// Each test construct a Max Segment Tree over 'a'.
/// Then checks if the 'key' of the root of the tree is
/// the correct one (the max over all elems in 'a')
#[cfg(test)]
mod max_segment_tree_tests {
    use crate::SegTree;

    #[test]
    fn mst_1() {
        // [TEST- 1] The constructed tree should be:
        //         2
        //       /   \
        // A =  1     2
        // p =  0     1
        let a = vec![1, 2];
        let mut tree = SegTree::empty_tree();
        tree.max_build(&a);
        if let Some(idx) = tree.root_idx {
            assert_eq!(tree.nodes[idx].key, 2)
        }
    }

    #[test]
    fn mst_2() {
        // [TEST- 2] The constructed tree should be:
        //           3
        //         /   \
        //        3     \
        //       / \     \
        // A =  1  3      2
        // p =  0  1      2
        let a = vec![1, 3, 2];
        let mut tree = SegTree::empty_tree();
        tree.max_build(&a);
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
        // [TEST- 3] The constructed tree should be:
        //            4
        //          /   \
        //         4     3
        //       /  \   /  \
        // A =  4   2   3   1
        // p =  0   1   2   3
        let a = vec![4, 2, 3, 1];
        let mut tree = SegTree::empty_tree();
        tree.max_build(&a);
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
        // [TEST- 4] The constructed tree should be:
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
        tree.max_build(&a);
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
        // [TEST- 5] The constructed tree should be:
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
        tree.max_build(&a);
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
