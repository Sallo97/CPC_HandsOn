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
use std::{cmp, collections::HashMap};

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
        if a.is_empty() {
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
    key: HashMap<usize, usize>,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
}

impl FreqNode {
    /// Base constructor
    /// TODO add better description
    fn new_leaf(a: &Vec<isize>, pos: usize) -> Self {
        let mut map = HashMap::new();
        let idx = usize::try_from(a[pos]).unwrap();
        map.insert(idx, 1);
        Self {
            key: map,
            children: (None, None),
            range: (pos, pos),
        }
    }

    /// TODO add better description
    fn new_node(
        nodes: (&FreqNode, &FreqNode),
        indexes: (usize, usize),
        range: (usize, usize),
    ) -> Self {
        // ∀i in [0, n-1].temp[i] = a[i] + b[i]
        let (map_l, map_r) = (&nodes.0.key, &nodes.1.key);
        let mut map: HashMap<usize, usize> =
            HashMap::with_capacity(cmp::max(map_l.len(), map_r.len()));

        // Scan all keys in map_l
        for (&k, &v) in map_l.iter() {
            println!("left with ({k} ,{v})");
            map.insert(k, v);
        }

        // Scan all keys in map_l
        for (&k, &v) in map_r.iter() {
            let mut val = v;
            if map.contains_key(&k) {
                val += map.get(&k).unwrap();
            }
            map.insert(k, val);
        }

        // Create and return self
        Self {
            key: map,
            children: (Some(indexes.0), Some(indexes.1)),
            range: (range.0, range.1),
        }
    }

    /// A node as as `key` an HashTable of pairs <`s`,`p`> s.t.
    /// - s = [0, #segments]
    /// - p = # of positions having s segments
    /// key(k) >= 1 -> 1, 0
    fn exists_positions(&self, k: usize) -> usize {
        if self.key.contains_key(&k) && *self.key.get(&k).unwrap() >= 1 {
            return 1;
        }
        0
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
    pub fn new(s: Vec<(usize, usize)>) -> Option<Self> {
        // Check that s is not empty
        if s.is_empty() {
            eprintln!("Empty set passed, no tree will be constructed");
            return None;
        }

        let mut tree = FreqSTree::empty_new();
        let a = FreqSTree::build_seg_array(s);
        tree.root = Some(tree.h_build(&a, 0, a.len() - 1));
        Some(tree)
    }

    /// Given a set of segments `s_set` = {s1; ...; sn}
    /// s.t each si = (l, r) where 0 <= l <= r <= n-1.
    /// The fn constructs an array `a[0, n-1]` s.t. each
    /// `a[i]` = # segments overlapping in position i
    /// # Assumptions
    fn build_seg_array(s_set: Vec<(usize, usize)>) -> Vec<isize> {
        let n = s_set.len();

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
            self.nodes.push(FreqNode::new_leaf(a, l));
        }
        // Inductive Case - Internal Node
        else {
            let m = (l + r) / 2;
            let lchd = self.h_build(&a, l, m);
            let rchd = self.h_build(&a, m + 1, r);

            self.nodes.push(FreqNode::new_node(
                (&self.nodes[lchd], &self.nodes[rchd]),
                (lchd, rchd),
                (l, r),
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
        if q_range.1 < c_range.0 || c_range.1 < q_range.0 {
            0
        }
        // Base Case #2 - Total Overlap
        else if q_range.0 <= c_range.0 && c_range.1 <= q_range.1 {
            self.nodes[idx].exists_positions(k)
        }
        // Iterative Case - Partial Overlap
        else {
            let m = (c_range.0 + c_range.1) / 2;

            // Part of the solution in the LEFT SIDE
            let sol_l = if q_range.0 <= m {
                let idx_l = self.nodes[idx].children.0.unwrap();
                let r = cmp::min(q_range.1, m);
                self.h_is_there((q_range.0, r), idx_l, k)
            } else {
                0
            };

            if sol_l == 1 {
                return 1;
            }

            // Part of the solution in the RIGHT SIDE
            let sol_r = if q_range.1 > m {
                let idx_r = self.nodes[idx].children.1.unwrap();
                let l = cmp::max(q_range.0, m);
                self.h_is_there((l, q_range.1), idx_r, k)
            } else {
                0
            };

            sol_r
        }
    }

    /// TODO Add better description
    pub fn is_there(&self, q_range: (usize, usize), k: usize) -> usize {
        let idx = self.root.unwrap();

        // Check if the range is indexed by the tree
        if !(q_range.0 >= self.nodes[idx].range.0 && q_range.1 <= self.nodes[idx].range.1) {
            eprintln!("Range not indexed by the tree!");
            return 0;
        }
        self.h_is_there(q_range, idx, k)
    }
}

/// A set of tests for constructors of `FreqNode`
/// For each test we provide the array `A[1,n]` of segments overlapping position
/// and construct a leaf or internal node according to `A`
#[cfg(test)]
mod freq_node_tests {
    use crate::FreqNode;

    #[test]
    fn fnt_1() {
        // [TEST - 1]
        // In this test we produce all the leaf generated by A s.t.
        // A = [1, 1, 2, 3, 3, 2, 1]
        // for i in [0, n-1]
        // for all j in [0,n-1].leaf_i[j] = { 1 if j=a[i] }
        //                                  { 0 otherwise }
        let a = vec![1, 1, 2, 3, 3, 2, 1];
        let leaf_0 = FreqNode::new_leaf(&a, 0);
        assert_eq!(leaf_0.key.len(), 1);
        assert_eq!(*leaf_0.key.get(&1).unwrap(), 1);

        let leaf_1 = FreqNode::new_leaf(&a, 1);
        assert_eq!(leaf_1.key.len(), 1);
        assert_eq!(*leaf_1.key.get(&1).unwrap(), 1);

        let leaf_2 = FreqNode::new_leaf(&a, 2);
        assert_eq!(leaf_2.key.len(), 1);
        assert_eq!(*leaf_2.key.get(&2).unwrap(), 1);

        let leaf_3 = FreqNode::new_leaf(&a, 3);
        assert_eq!(leaf_3.key.len(), 1);
        assert_eq!(*leaf_3.key.get(&3).unwrap(), 1);

        let leaf_4 = FreqNode::new_leaf(&a, 4);
        assert_eq!(leaf_4.key.len(), 1);
        assert_eq!(*leaf_4.key.get(&3).unwrap(), 1);

        let leaf_5 = FreqNode::new_leaf(&a, 5);
        assert_eq!(leaf_5.key.len(), 1);
        assert_eq!(*leaf_5.key.get(&2).unwrap(), 1);

        let leaf_6 = FreqNode::new_leaf(&a, 6);
        assert_eq!(leaf_6.key.len(), 1);
        assert_eq!(*leaf_6.key.get(&1).unwrap(), 1)
    }

    #[test]
    fn fnt_2() {
        // [TEST - 2]
        // Given the leaf from the previous test we
        // produce the nodes whose childesn are the leaf
        // pairwise (node_1 will have as children leaf_0 and leaf_1)
        let a = vec![1, 1, 2, 3, 3, 2, 1];
        let leaf_0 = FreqNode::new_leaf(&a, 0);
        let leaf_1 = FreqNode::new_leaf(&a, 1);
        let leaf_2 = FreqNode::new_leaf(&a, 2);
        let leaf_3 = FreqNode::new_leaf(&a, 3);
        let leaf_4 = FreqNode::new_leaf(&a, 4);
        let leaf_5 = FreqNode::new_leaf(&a, 5);
        let leaf_6 = FreqNode::new_leaf(&a, 6);

        let node_0 = FreqNode::new_node((&leaf_0, &leaf_1), (0, 1), (0, 1));
        assert_eq!(node_0.key.len(), 1);
        assert_eq!(*node_0.key.get(&1).unwrap(), 2);

        let node_1 = FreqNode::new_node((&leaf_2, &leaf_3), (2, 3), (2, 3));
        assert_eq!(node_1.key.len(), 2);
        assert_eq!(*node_1.key.get(&2).unwrap(), 1);
        assert_eq!(*node_1.key.get(&3).unwrap(), 1);

        let node_2 = FreqNode::new_node((&leaf_4, &leaf_5), (4, 5), (4, 5));
        assert_eq!(*node_2.key.get(&2).unwrap(), 1);
        assert_eq!(*node_2.key.get(&3).unwrap(), 1);

        let node_3 = FreqNode::new_node((&node_2, &leaf_6), (7, 6), (4, 6));
        assert_eq!(*node_3.key.get(&1).unwrap(), 1);
        assert_eq!(*node_3.key.get(&2).unwrap(), 1);
        assert_eq!(*node_3.key.get(&3).unwrap(), 1);
    }
}

/// A set of tests for `is_there` method
/// For each test we construct a Frequency Segment Tree over a set of
/// segments `S` and test various queries over it.
/// For each test we provide a visual representation of the constructed
/// tree, specifying the queries proposed and the answers they should get
#[cfg(test)]
mod is_there_tests {
    use crate::FreqSTree;

    #[test]
    fn itt_1() {
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
        // Query: IsThere((0,5), 1) -> Answer: 1
        // Query: IsThere((4,6), 2) -> Answer: 1
        // Query: IsThere((2,6), 3) -> Answer: 1
        // Query: IsThere((3,6), 0) -> Answer: 0
        let s = vec![(0, 0), (1, 3), (2, 3), (3, 5), (4, 4), (4, 5), (6, 6)];
        let tree = FreqSTree::new(s).unwrap();

        let res_1 = tree.is_there((0, 5), 1);
        assert_eq!(res_1, 1);
        let res_2 = tree.is_there((4, 6), 2);
        assert_eq!(res_2, 1);
        let res_3 = tree.is_there((2, 6), 3);
        assert_eq!(res_3, 1);
        let res_4 = tree.is_there((3, 6), 0);
        assert_eq!(res_4, 0);
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
        let tree = FreqSTree::new(s).unwrap();
        let root_idx = tree.root.unwrap();
        // assert_eq!(tree.nodes[root_idx].key, vec![0, 3, 2, 2, 0, 0, 0]);
        // {
        //     // Checking LEFT Subtree
        //     let root_idx = tree.nodes[root_idx].children.0.unwrap();
        //     assert_eq!(tree.nodes[root_idx].key, vec![0, 2, 1, 1, 0, 0, 0]);
        //     let left_idx = tree.nodes[root_idx].children.0.unwrap();
        //     let right_idx = tree.nodes[root_idx].children.1.unwrap();
        //     assert_eq!(tree.nodes[left_idx].key, vec![0, 2, 0, 0, 0, 0, 0]);
        //     assert_eq!(tree.nodes[right_idx].key, vec![0, 0, 1, 1, 0, 0, 0])
        // }

        // {
        //     // Checking RIGHT Subtree
        //     let root_idx = tree.nodes[root_idx].children.1.unwrap();
        //     assert_eq!(tree.nodes[root_idx].key, vec![0, 1, 1, 1, 0, 0, 0]);
        //     let left_idx = tree.nodes[root_idx].children.0.unwrap();
        //     let right_idx = tree.nodes[root_idx].children.1.unwrap();
        //     assert_eq!(tree.nodes[left_idx].key, vec![0, 0, 1, 1, 0, 0, 0]);
        //     assert_eq!(tree.nodes[right_idx].key, vec![0, 1, 0, 0, 0, 0, 0])
        // }
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
        // Edge case we try to pass and empty set of strings
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
    fn ut_2() {
        // [TEST - 2] The constructed tree should be:
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
