/// This code implements the solutions for the second HandsOn of
/// the course "Competitive Programming and Contest" 2024/25
/// course held at at the University of Pisa.
///
/// [PROBLEM #1 - Min and Max]
/// Given an array A[1,n] of n positive integers s.t each each x in A = O(n),
/// build a data structure that answers in O(log(n)) time the following queries:
/// - Update(i,j,T): ∀k in [1,n].A[k] = min(A[k], T)
/// - Max(i, j) : returns the largest value in A[i...j]
///
/// [PROBLEM #2 - Is There]
/// Given a set of n segments S = {s1; ...; sn} s.t each si = (li, ri)
/// where 0 <=li <= ri <= n-1, build a data structure to answer in O(log(n))
/// time the following query:
/// IsThere(i,j,k) = { 1     if ∃p in [i,j] s.t exactly k segments }
///                                             overlap position p }
///                  { 0     otherwise                             }
use std::{cmp, collections::HashMap};

/// Represents a node in the Max Segment Tree.
/// Each node includes:
/// - `key`: The maximum value among its children's keys.
///          If the node is the `i`-th leaf, then `key = a[i]`.
/// - `children`: A pair of indexes representing the node's children.
///               If the node is a leaf, `children = (None, None)`.
/// - `range`: The range of indices in the array `a` indexed by the node.
/// - `update`: abstract that in the Lazy Tree here there is pending update (v, l, r) where
///             * v = the value that the subtrees rooted at the current node needs to update
///             * l = boolean specifying if the left subtree as been updated (true) or not (false)
///             * r = boolean specifying if the right subtree as been updated (true) or not (false)
struct MaxNode {
    key: usize,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
    pending: Option<(usize, bool, bool)>,
}

impl MaxNode {
    /// A base constructor requiring to pass every
    /// value of the node manually.
    fn new(key: usize, children: (Option<usize>, Option<usize>), range: (usize, usize)) -> Self {
        Self {
            key,
            children,
            range,
            pending: None,
        }
    }

    /// Tries to update the key, if the node is an internal node,
    /// update the `pending` value s.t. when a max query will traverse
    /// one of the children of the node, it will updated them with the new key
    /// # Returns
    /// The new key of the node.
    fn set_lazy_update(&mut self, new: usize) -> usize {
        let is_updated = self.set_key(new);
        // If its an internal node AND its value as been modified
        // then we must update `pending`
        if (self.range.0 != self.range.1) && is_updated {
            self.pending = Some((self.key, false, false));
        }
        self.key
    }

    /// TODO Add better description
    /// # Returns
    /// `true` if the key has been updated
    /// `false` otherwise
    fn set_key(&mut self, new: usize) -> bool {
        if new >= self.key {
            false
        } else {
            self.key = new;
            true
        }
    }

    /// Checks if there is a pending update for the `is_left` subtree
    /// and if so returns the value to update.
    fn get_lazy_update(&self, is_left: bool) -> Option<usize> {
        if let Some((val, l_update, r_update)) = self.pending {
            match is_left {
                true => {
                    // LEFT Subtree
                    if !l_update {
                        self.pending.unwrap().1 = true;
                        return Some(val);
                    } else {
                        return None;
                    }
                }
                false => {
                    // RIGHT Subtree
                    if !r_update {
                        self.pending.unwrap().2 = true;
                        return Some(val);
                    } else {
                        return None;
                    }
                }
            }
        } else {
            None
        }
    }
}

/// Represents a Maximum Segment Tree.
/// ∀node in MaxSTree.node.key = max value in A[node.range].
/// The tree includes:
/// - `nodes`: A vector containing all the nodes of the tree.
/// - `root`: The index of the root node in the `nodes` vector.
pub struct MaxSTree {
    nodes: Vec<MaxNode>,
    root: Option<usize>,
}

impl MaxSTree {
    /// Initializes an empty tree instance.
    fn empty_new() -> Self {
        Self {
            nodes: Vec::new(),
            root: None,
        }
    }

    /// Base constructor which given a vector of n positive integers `a`
    /// s.t. each ∀x in `a`. 0 < x <= n, constructs a Max Segment Tree
    /// indexing the elements in `a`.
    /// # Returns
    /// If `a` is as requented a `Some(MaxSegTree)` instance, otherwise return
    /// `None` indicating that no tree can be constructed.
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

    /// Helper fn which recursively construct a Max Segment Tree over
    /// a passed vector of positive integers `a`.
    /// # Returns
    /// The index of the created node in the Max Segment Tree.
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

    /// Given a `q_range` = (l, r) returns `x` s.t. x = max value
    /// indexed by the tree in [l,r].
    pub fn max(&mut self, q_range: (usize, usize)) -> Option<usize> {
        let q_range = (q_range.0 - 1, q_range.1 - 1);
        let idx = self.root.unwrap();

        // Check if the range is indexed by the tree
        if !(q_range.0 >= self.nodes[idx].range.0 && q_range.1 <= self.nodes[idx].range.1) {
            eprintln!("Range not indexed by the tree!");
            return None;
        }

        self.h_max(q_range, idx, None)
    }

    /// A helper recursive fn that returns the maximum value within the range
    /// `q_range` = (l, r) for the tree whose root is at index `idx`. If the
    /// `q_range` is out of range it returns `None`.
    /// `new` when executing a lazy update update the visited node.
    fn h_max(&mut self, q_range: (usize, usize), idx: usize, new: Option<usize>) -> Option<usize> {
        let c_range = self.nodes[idx].range;

        // Update node if new != None
        if let Some(val) = new {
            self.nodes[idx].set_lazy_update(val);
        }

        // Base Case #1 - No Overlap
        if q_range.1 < c_range.0 || c_range.1 < q_range.0 {
            None
        }
        // Base Case #2 - Total Overlap
        else if (q_range.0 <= c_range.0) && (c_range.1 <= q_range.1) {
            Some(self.nodes[idx].key)
        }
        // Iterative Case - Partial Overlap
        else {
            let m = (c_range.0 + c_range.1) / 2;

            // Part of the solution in the LEFT SIDE
            let sol_l = if q_range.0 <= m {
                // If there is a pending update for the left side,
                // pass it, otherwise pass None
                let new = self.nodes[idx].get_lazy_update(true);
                let idx = self.nodes[idx].children.0.unwrap();
                let r = cmp::min(q_range.1, m);
                self.h_max((q_range.0, r), idx, new)
            } else {
                None
            };

            // Part of the solution in the RIGHT SIDE
            let sol_r = if q_range.1 > m {
                // If there is a pending update for the right side,
                // pass it , otherwise pass None
                let new = self.nodes[idx].get_lazy_update(false);
                let idx = self.nodes[idx].children.1.unwrap();
                let l = cmp::max(q_range.0, m);
                self.h_max((l, q_range.1), idx, new)
            } else {
                None
            };

            // Merge the two partial solutions
            cmp::max(sol_l, sol_r)
        }
    }

    /// Given `u_range` = (l, r) and a value `t` then if (l,r)
    /// are within the range of the tree, updates it s.t.
    /// ∀k in [l,r].A[k] = min(A[k], t).
    pub fn update(&mut self, q_range: (usize, usize), t: usize) {
        let q_range = (q_range.0 - 1, q_range.1 - 1);
        let idx = self.root.unwrap();

        // Check if the range is indexed by the tree
        if !(q_range.0 >= self.nodes[idx].range.0 && q_range.1 <= self.nodes[idx].range.1) {
            eprintln!("Range not indexed by the tree!");
        }

        self.h_update(q_range, t, idx);
    }

    /// Helper recursive fn s.t given `u_range` = (l,r) and a value `t`,
    /// then if (l,r) are within the range of the tree rooted at `idx`, updates
    /// the tree s.t.
    /// ∀k in [l,r].A[k] = min(A[k], t).
    /// # Returns
    /// the (possibly new) key value of the terminating node
    fn h_update(&mut self, q_range: (usize, usize), t: usize, idx: usize) -> Option<usize> {
        let c_range = self.nodes[idx].range;

        // Base Case #1 - No overlap
        if q_range.1 < c_range.0 || c_range.1 < q_range.0 {
            Some(self.nodes[idx].key)
        }
        // Base Case #2 - Total Overlap
        else if q_range.0 <= c_range.0 && c_range.1 <= q_range.1 {
            Some(self.nodes[idx].set_lazy_update(t))
        }
        // Iterative Case - Partial Overlap
        else {
            // We need to pass the lazy update lower
            // while updating the current node
            let m = (c_range.0 + c_range.1) / 2;

            // TODO VISITA SEMPRE SIA DESTRA CHE SINISTRA
            // SENNÒ NON SETTI IL VALORE CORRETTO

            // Part of the solution in the LEFT SIDE
            let sol_l = if q_range.0 <= m {
                let idx = self.nodes[idx].children.0.unwrap();
                let r = cmp::min(q_range.1, m);
                self.h_update((q_range.0, r), t, idx)
            } else {
                let idx = self.nodes[idx].children.0.unwrap();
                Some(self.nodes[idx].key)
            };

            // Part of the solution in the RIGHT SIDE
            let sol_r = if q_range.1 > m {
                let idx = self.nodes[idx].children.1.unwrap();
                let l = cmp::max(q_range.0, m);
                self.h_update((l, q_range.1), t, idx)
            } else {
                let idx = self.nodes[idx].children.1.unwrap();
                Some(self.nodes[idx].key)
            };

            // Merge the two partial solutions
            self.nodes[idx].key = cmp::max(sol_l, sol_r).unwrap_or(self.nodes[idx].key);
            Some(self.nodes[idx].key)
        }
    }
}

/// Represents a node in the Frequency Segment Tree.
/// Each node includes:
/// - `key`: A hash map with pairs `<k, p>` for the range covered by the node, where:
///   * `k`: The number of overlapping segments at a position (`0 <= k <= n`).
///   * `p`: # positions within the node's range where exactly `k` segments overlap.
/// - `children`: A pair of indexes representing the node's children.
///               If the node is a leaf, `children = (None, None)`.
/// - `range`: The range of position within the set of segments indexed by the node.
struct FreqNode {
    key: HashMap<usize, usize>,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
}

impl FreqNode {
    /// For a given array `a'[0, n - 1], where each element
    /// `a[i]`= # of segments overlapping at position `i`,
    /// and a specified position `pos`:
    /// construct a leaf node s.t.:
    /// - `leaf.range = (pos, pos)`.
    /// - `leaf.key` = an hash map containing only the pair `<a[pos], 1>`.
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

    /// Constructs an internal node in the Frequency Segment Tree.
    /// The node's `key` is a hash map created by merging the `key` maps of its child nodes,
    /// which are specified by the `indexes` within the `nodes` array.
    /// The resulting node represents the segments indexed within the specified `range`.
    fn new_node(
        nodes: (&FreqNode, &FreqNode),
        indexes: (usize, usize),
        range: (usize, usize),
    ) -> Self {
        let (map_l, map_r) = (&nodes.0.key, &nodes.1.key);
        let mut map: HashMap<usize, usize> =
            HashMap::with_capacity(cmp::max(map_l.len(), map_r.len()));

        // Scan all keys in map_l
        for (&k, &v) in map_l.iter() {
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

    /// Checks if the node contains in its hash map a
    /// pair <k, p> s.t. p >= 1. If so returns 1, otherwise 0.
    /// Formally:
    /// key(k) >= 1 -> 1, 0
    fn exists_positions(&self, k: usize) -> usize {
        if self.key.contains_key(&k) && *self.key.get(&k).unwrap() >= 1 {
            return 1;
        }
        0
    }
}

/// Represents a Frequency Segment Tree.
/// ∀node in FreqSTree:node.key = map containing all the pairs <k,p>
/// for the range indexed by the node where:
///  * `k`: The number of overlapping segments at a position (`0 <= k <= n`).
///  * `p`: # positions within the node's range where exactly `k` segments overlap.
/// Its implementation uses:
/// - `nodes`: A vector containing all the nodes of the tree.
/// - `root`: The index of the root node in the `nodes` vector.
pub struct FreqSTree {
    nodes: Vec<FreqNode>,
    root: Option<usize>,
}

impl FreqSTree {
    /// Initializes an empty tree instance.
    fn empty_new() -> Self {
        Self {
            nodes: Vec::new(),
            root: None,
        }
    }

    /// Given a set of n segments `s` = {s1; ...; sn} s.t each si = (li, ri)
    /// where 0 <=li <= ri <= n-1, initialize a Frequency Segment Tree
    /// indexing all elements in `s`.
    /// If `s` is  as requented returns a `Some(FreqSegTree)` instance, otherwise return
    /// `None` indicating that no tree can be constructed.
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

    /// Given a set of segments `s_set` = {s1; ...; sn} s.t each
    ///  si = (l, r) where 0 <= l <= r <= n-1, constructs an array
    /// `a[0, n-1]` s.t. each `a[i]` = # segments overlapping in position i
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

    /// Constructs a Frequency Segment Tree indexing segments in [`l`,`r`]
    /// from a given array of positions `a` s.t. each `a[i]` = # segments
    /// overlapping in position i.
    fn h_build(&mut self, a: &Vec<isize>, l: usize, r: usize) -> usize {
        // Base Case - Leaf
        if l == r {
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

    /// Given `q_range` = (i,j) and a value `k` returns :
    /// - 1: if there exists a position p in [i,j] in the tree
    ///      s.t. exactly `k` segments overlap position p
    /// - 0: otherwise
    pub fn is_there(&self, q_range: (usize, usize), k: usize) -> usize {
        let idx = self.root.unwrap();

        // Check if the range is indexed by the tree
        if !(q_range.0 >= self.nodes[idx].range.0 && q_range.1 <= self.nodes[idx].range.1) {
            eprintln!("Range not indexed by the tree!");
            return 0;
        }
        self.h_is_there(q_range, idx, k)
    }

    /// Given `q_range` = (i,j) and a value `k` returns :
    /// - 1: if there exists a position p in [i,j] in the subtree indexed in `idx`
    ///      s.t. exactly `k` segments overlap position p
    /// - 0: otherwise
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
}

/// A set of tests for constructors of `FreqNode`
/// For each test we provide the vector `a[0,n - 1]`
/// of segments overlapping position and construct a
/// leaf or internal node according to `a`.
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
        assert_eq!(node_2.key.len(), 2);
        assert_eq!(*node_2.key.get(&2).unwrap(), 1);
        assert_eq!(*node_2.key.get(&3).unwrap(), 1);

        let node_3 = FreqNode::new_node((&node_2, &leaf_6), (7, 6), (4, 6));
        assert_eq!(node_3.key.len(), 3);
        assert_eq!(*node_3.key.get(&1).unwrap(), 1);
        assert_eq!(*node_3.key.get(&2).unwrap(), 1);
        assert_eq!(*node_3.key.get(&3).unwrap(), 1);
    }
}

/// A set of tests for `is_there` method
/// For each test we construct a Frequency Segment Tree over a set of
/// segments `S` and test various queries over it.
/// For each test we provide a visual representation of the constructed
/// tree, specifying the queries proposed and the answers they should get.
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

/// A set of tests for constructing Frequency Segment Tree.
/// Each test construct a FreqSegTree over 'a'.
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
        assert_eq!(tree.nodes[root_idx].key.len(), 3);
        assert_eq!(*tree.nodes[root_idx].key.get(&1).unwrap(), 3);
        assert_eq!(*tree.nodes[root_idx].key.get(&2).unwrap(), 2);
        assert_eq!(*tree.nodes[root_idx].key.get(&3).unwrap(), 2);
        {
            // Checking LEFT Subtree
            let root_idx = tree.nodes[root_idx].children.0.unwrap();
            assert_eq!(tree.nodes[root_idx].key.len(), 3);
            assert_eq!(*tree.nodes[root_idx].key.get(&1).unwrap(), 2);
            assert_eq!(*tree.nodes[root_idx].key.get(&2).unwrap(), 1);
            assert_eq!(*tree.nodes[root_idx].key.get(&3).unwrap(), 1);

            let left_idx = tree.nodes[root_idx].children.0.unwrap();
            assert_eq!(tree.nodes[left_idx].key.len(), 1);
            assert_eq!(*tree.nodes[left_idx].key.get(&1).unwrap(), 2);

            let right_idx = tree.nodes[root_idx].children.1.unwrap();
            assert_eq!(tree.nodes[right_idx].key.len(), 2);
            assert_eq!(*tree.nodes[right_idx].key.get(&2).unwrap(), 1);
            assert_eq!(*tree.nodes[right_idx].key.get(&3).unwrap(), 1);
        }

        {
            // Checking RIGHT Subtree
            let root_idx = tree.nodes[root_idx].children.1.unwrap();
            assert_eq!(tree.nodes[root_idx].key.len(), 3);
            assert_eq!(*tree.nodes[root_idx].key.get(&1).unwrap(), 1);
            assert_eq!(*tree.nodes[root_idx].key.get(&2).unwrap(), 1);
            assert_eq!(*tree.nodes[root_idx].key.get(&3).unwrap(), 1);

            let left_idx = tree.nodes[root_idx].children.0.unwrap();
            assert_eq!(tree.nodes[left_idx].key.len(), 2);
            assert_eq!(*tree.nodes[left_idx].key.get(&2).unwrap(), 1);
            assert_eq!(*tree.nodes[left_idx].key.get(&3).unwrap(), 1);

            let right_idx = tree.nodes[root_idx].children.1.unwrap();
            assert_eq!(tree.nodes[right_idx].key.len(), 1);
            assert_eq!(*tree.nodes[right_idx].key.get(&1).unwrap(), 1);
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
        // Edge case we try to pass and empty set of strings
        // Solution = [] EMPTY
        let s = vec![];
        let a = FreqSTree::build_seg_array(s);
        let empty: Vec<isize> = Vec::new();
        assert_eq!(empty, a)
    }
}

/// A set of tests for 'max' function.
/// Each test checks if the returned value is the max value
/// indexed by the tree in the requested range.
/// For each test a visual representation of the tree is provided.
/// !<node>! Specifies a node used to retrive the solution
#[cfg(test)]
mod max_query_tests {
    use crate::MaxSTree;

    #[test]
    fn mt_0() {
        // Query = max(3,6)
        // Solution = 4
        let a = vec![9, 4, 1, 6, 5, 10, 6, 8, 7, 4];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((6, 7), 10);
        assert_eq!(tree.max((5, 8)), Some(10));
        assert_eq!(tree.max((8, 8)), Some(8));
        assert_eq!(tree.max((4, 10)), Some(10));
        assert_eq!(tree.max((6, 8)), Some(10));
        assert_eq!(tree.max((10, 10)), Some(4));
        tree.update((3, 10), 4);
        assert_eq!(tree.max((2, 4)), Some(4));
        assert_eq!(tree.max((1, 9)), Some(9));
        assert_eq!(tree.max((9, 10)), Some(4));
    }

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
        // p =  1   2    3     4    5   6
        // Query = max(3,6)
        // Solution = 4
        let a = vec![6, 5, 4, 2, 1, 3];
        let mut tree = MaxSTree::new(&a).unwrap();
        assert_eq!(tree.max((3, 6)), Some(4));
    }

    #[test]
    fn mt_2() {
        // [TEST -2] The constructed tree should be:
        //           3
        //          / \
        //         3   \
        //       /  \   \
        // A =  3    1   2
        // p =  1   2    3
        // Query = max(2,5)
        // Solution = None, the query goes out of range!
        let a = vec![3, 1, 2];
        let mut tree = MaxSTree::new(&a).unwrap();
        assert_eq!(tree.max((2, 5)), None);
    }

    #[test]
    fn mt_3() {
        // [TEST - 2] The constructed tree should be:
        //           3            2
        //          / \          / \
        //         3   \  =>    2   \
        //       /  \   \      / \   \
        // A =  3    1   2    2   1   2
        // p =  1   2    3    1   2   3
        // Query = max(2,5)
        // Solution = None, the query goes out of range!
        let a = vec![3, 1, 2];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((1, 2), 2);
        // Check Max Query
        assert_eq!(tree.max((1, 1)), Some(2));
        // Check tree
        let root = tree.root.unwrap();
        assert_eq!(tree.nodes[root].key, 2);
        {
            // Left subtree
            let root = tree.nodes[root].children.0.unwrap();
            assert_eq!(tree.nodes[root].key, 2);
            let left_idx = tree.nodes[root].children.0.unwrap();
            assert_eq!(tree.nodes[left_idx].key, 2);
            let right_idx = tree.nodes[root].children.1.unwrap();
            assert_eq!(tree.nodes[right_idx].key, 1);
        }
        {
            // Right subtree
            let root = tree.nodes[root].children.1.unwrap();
            assert_eq!(tree.nodes[root].key, 2);
        }
    }
}

/// A set of tests for the lazy update of the Max Segment Tree
/// For each test a visual representation of the tree is provided

#[cfg(test)]
mod update_max_segment_tree_tests {
    use crate::MaxSTree;

    #[test]
    fn ust_1() {
        // [TEST - 1] The constructed tree should be:
        //                  6                          4
        //            /          \                 /       \
        //           5            6              !4!         4
        //          / \          /  \    =>     /  \       /  \
        //         3   \        6    \         3    \     !4!  \
        //       /  \   \      /  \   \       / \    \    / \   \
        // A =  1   3    5    2    6   4     1   3    5  2   6   4
        // p =  0   1    2    3    4   5     0   1    2  3   4   5
        // Query = Update((1, 5), 4)
        let a = vec![1, 3, 5, 2, 6, 4];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((1, 5), 4);

        // Visit of the tree
        let idx = tree.root.unwrap();
        assert_eq!(tree.nodes[idx].key, 4);
        {
            // Left subtree (4)
            let idx = tree.nodes[idx].children.0.unwrap();
            assert_eq!(tree.nodes[idx].key, 4);
            let left_idx = tree.nodes[idx].children.0.unwrap();
            assert_eq!(tree.nodes[left_idx].key, 3);
            let right_idx = tree.nodes[idx].children.1.unwrap();
            assert_eq!(tree.nodes[right_idx].key, 5);
            {
                // Left subtree (3)
                let root = left_idx; //(3)
                let left_idx = tree.nodes[root].children.0.unwrap();
                assert_eq!(tree.nodes[left_idx].key, 1);
                let right_idx = tree.nodes[root].children.1.unwrap();
                assert_eq!(tree.nodes[right_idx].key, 3);
            }
        }

        {
            // Right subtree (4)
            let idx = tree.nodes[idx].children.1.unwrap();
            assert_eq!(tree.nodes[idx].key, 4);
            let left_idx = tree.nodes[idx].children.0.unwrap();
            assert_eq!(tree.nodes[left_idx].key, 4);
            let right_idx = tree.nodes[idx].children.1.unwrap();
            assert_eq!(tree.nodes[right_idx].key, 4);
            {
                // Left subtree(4)
                let root = left_idx; //(4)
                let left_idx = tree.nodes[root].children.0.unwrap();
                assert_eq!(tree.nodes[left_idx].key, 2);
                let right_idx = tree.nodes[root].children.1.unwrap();
                assert_eq!(tree.nodes[right_idx].key, 6);
            }
        }
    }

    #[test]
    fn ust_2() {
        // [TEST - 2] The constructed tree should be:
        //           3
        //          / \
        //         3   \
        //       /  \   \
        // A =  3    1   2
        // p =  1   2    3
        // Query = Update((1,3), 4)
        // Solution = None, the query goes out of range!
        let a = vec![3, 1, 2];
        let mut tree = MaxSTree::new(&a).unwrap();
        tree.update((1, 3), 4);
        let root = tree.root.unwrap();
        assert_eq!(tree.nodes[root].key, 3)
    }

    #[test]
    fn ust_3() {
        // [TEST - 2] The constructed tree should be:
        //         3             2
        //       /   \   =>    /   \
        // A =  3     3       2     3
        // p =  1     2       2     2
        // Query = Update((1, 2), 2)
        // Query = max((1,2))
        // Query = max((1,1))
        let a = vec![3, 3];
        let tree = MaxSTree::new(&a);
        let mut tree = tree.unwrap();
        tree.update((1, 2), 2);
        tree.max((1, 1));
        //tree.max((2, 2));

        // Visiting tree
        let root = tree.root.unwrap();
        assert_eq!(tree.nodes[root].key, 2);
        let left = tree.nodes[root].children.0.unwrap();
        assert_eq!(tree.nodes[left].key, 2);
        let right = tree.nodes[root].children.1.unwrap();
        assert_eq!(tree.nodes[right].key, 3)
    }

    #[test]
    fn ust_4() {
        // [TEST - 2] The constructed tree should be:
        //         3             2
        //       /   \   =>    /   \
        // A =  3     3       3     2
        // p =  1     2       2     2
        // Query = Update((1, 2), 2)
        // Query = max((1,2))
        // Query = max((2,2))
        let a = vec![3, 3];
        let tree = MaxSTree::new(&a);
        let mut tree = tree.unwrap();
        tree.update((1, 2), 2);
        tree.max((2, 2));

        // Visiting tree
        let root = tree.root.unwrap();
        assert_eq!(tree.nodes[root].key, 2);
        let left = tree.nodes[root].children.0.unwrap();
        assert_eq!(tree.nodes[left].key, 3);
        let right = tree.nodes[root].children.1.unwrap();
        assert_eq!(tree.nodes[right].key, 2)
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
