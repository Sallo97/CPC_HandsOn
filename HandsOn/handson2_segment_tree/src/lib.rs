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
/// - `pending`: boolean which states if the node contains a pending update
///              to pass to its children.
struct MaxNode {
    key: usize,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
    pending: bool,
}

impl MaxNode {
    /// A base constructor requiring to pass every
    /// value of the node manually.
    fn new(key: usize, children: (Option<usize>, Option<usize>), range: (usize, usize)) -> Self {
        Self {
            key,
            children,
            range,
            pending: false,
        }
    }

    /// Updates the current node's value by setting `node.key` to `min(new_val, node.key)`,
    /// instead of recursively updating the entire subtree rooted at this node.
    /// Marks the node as `pending`, indicating that its children need to be updated
    /// with the node's current value during future operations. For leaf nodes,
    /// no pending update is set as they have no children.
    fn lazy_update(&mut self, new_val: usize) {
        // If I'm not a leaf I have a pending update in my hands
        let (l, r) = self.range;
        if l != r {
            self.pending = true;
        }
        self.key = cmp::min(new_val, self.key);
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
        let (l, r) = (range.0, range.1);
        if l == r {
            // BASE CASE: LEAF
            self.nodes.push(MaxNode::new(a[l], (None, None), (l, l)));
        } else {
            // INDUCTIVE CASE: Internal Node
            let m = (l + r) / 2;
            let lchd = self.h_build(&a, (l, m));
            let rchd = self.h_build(&a, (m + 1, r));
            let val = cmp::max(self.nodes[lchd].key, self.nodes[rchd].key);

            self.nodes
                .push(MaxNode::new(val, (Some(lchd), Some(rchd)), range));
        }
        self.nodes.len() - 1
    }

    /// If the node at index `idx` has a pending update, it
    /// propagates it lazily updating its children.
    fn propagate(&mut self, idx: usize) {
        if self.nodes[idx].pending {
            let key = self.nodes[idx].key;
            self.nodes[idx].pending = false;
            let idx_l = self.nodes[idx].children.0.unwrap();
            self.nodes[idx_l].lazy_update(key);
            let idx_r = self.nodes[idx].children.1.unwrap();
            self.nodes[idx_r].lazy_update(key);
        }
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
        self.h_max(q_range, idx)
    }

    /// A helper recursive fn that returns the maximum value within the range
    /// `q_range` = (l, r) for the tree whose root is at index `idx`. If the
    /// `q_range` is out of range it returns `None`.
    fn h_max(&mut self, q_range: (usize, usize), idx: usize) -> Option<usize> {
        let (c_l, c_r) = self.nodes[idx].range;
        let (q_l, q_r) = q_range;
        // If current node has a pending update, propagate it
        self.propagate(idx);
        // Base Case #1 - No Overlap
        if q_r < c_l || c_r < q_l {
            None
        }
        // Base Case #2 - Total Overlap
        else if q_l <= c_l && c_r <= q_r {
            Some(self.nodes[idx].key)
        }
        // Iterative Case - Partial Overlap
        else {
            let m = (c_l + c_r) / 2;

            // Part of the solution in the LEFT SIDE
            let sol_l = if q_l <= m {
                let idx = self.nodes[idx].children.0.unwrap();
                let r = cmp::min(q_r, m);
                self.h_max((q_l, r), idx)
            } else {
                None
            };

            // Part of the solution in the RIGHT SIDE
            let sol_r = if q_r > m {
                let idx = self.nodes[idx].children.1.unwrap();
                let l = cmp::max(q_l, m);
                self.h_max((l, q_r), idx)
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
    pub fn update(&mut self, u_range: (usize, usize), t: usize) {
        let u_range = (u_range.0 - 1, u_range.1 - 1);
        let idx = self.root.unwrap();
        self.h_update(u_range, t, idx);
    }

    /// Helper recursive fn s.t given `u_range` = (l,r) and a value `t`,
    /// then if (l,r) are within the range of the tree rooted at `idx`, updates
    /// the tree s.t.
    /// ∀k in [l,r].A[k] = min(A[k], t).
    fn h_update(&mut self, u_range: (usize, usize), t: usize, idx: usize) -> usize {
        let (c_l, c_r) = self.nodes[idx].range;
        let (q_l, q_r) = (u_range.0, u_range.1);

        // If current node has a pending update, propagate
        // it to its children
        self.propagate(idx);

        // Base Case #1 No Overlap
        if q_r < c_l || c_r < q_l {
            self.nodes[idx].key
        }
        // Base Case #2 Total Overlap
        else if q_l <= c_l && c_r <= q_r {
            let new_val = cmp::min(t, self.nodes[idx].key);
            self.nodes[idx].lazy_update(new_val);
            self.nodes[idx].key
        }
        // Iterative Case Partial Overlap
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
