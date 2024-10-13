use std::cmp::max;

pub struct Node {
    key: u32,
    id_left: Option<usize>,
    id_right: Option<usize>,
}

impl Node {
    fn new(key: u32) -> Self {
        Self {
            key,
            id_left: None,
            id_right: None,
        }
    }
}

pub struct Tree {
    nodes: Vec<Node>,
}

impl Tree {
    pub fn with_root(key: u32) -> Self {
        Self {
            nodes: vec![Node::new(key)],
        }
    }

    /// Adds a child to the node with `parent_id` and returns the id of the new node.
    /// The new node has the specified `key`. The new node is the left  child of the
    /// node `parent_id` iff `is_left` is `true`, the right child otherwise.
    ///
    /// # Panics
    /// Panics if the `parent_id` does not exist, or if the node `parent_id ` has
    /// the child already set.
    pub fn add_node(&mut self, parent_id: usize, key: u32, is_left: bool) -> usize {
        assert!(
            parent_id < self.nodes.len(),
            "Parent node id does not exist"
        );
        if is_left {
            assert!(
                self.nodes[parent_id].id_left == None,
                "Parent node has the left child already set"
            );
        } else {
            assert!(
                self.nodes[parent_id].id_right == None,
                "Parent node has the right child already set"
            );
        }

        let child_id = self.nodes.len();
        self.nodes.push(Node::new(key));

        let child = if is_left {
            &mut self.nodes[parent_id].id_left
        } else {
            &mut self.nodes[parent_id].id_right
        };

        *child = Some(child_id);

        child_id
    }

    /// Returns the sum of all the keys in the tree
    pub fn sum(&self) -> u32 {
        self.rec_sum(Some(0))
    }

    /// A private recursive function that computes the sum of
    /// nodes in the subtree rooted at `node_id`.
    fn rec_sum(&self, node_id: Option<usize>) -> u32 {
        if let Some(id) = node_id {
            assert!(id < self.nodes.len(), "Node id is out of range");
            let node = &self.nodes[id];

            let sum_left = self.rec_sum(node.id_left);
            let sum_right = self.rec_sum(node.id_right);

            return sum_left + sum_right + node.key;
        }

        0
    }

    /// A private recursive function that computes for the tree starting at the node
    /// with index `node_idx` the minimum value, maximum value in it and if the tree
    /// is a BST or not.
    /// # Arguments
    /// * `node_idx` - the idx of the current node.
    /// * `min`  - the minimum found so far (at the start should be the key of the starting node).
    /// * `max`  - the maximum found so far (at the start should be the key of the starting node).
    /// # Return
    /// Returns the triple (min,max, bst) s.t.:
    /// * `min`  - the current minimum for the explored tree.
    /// * `max`  - the current maximum for the explored tree.
    /// * `bst` - a bool stating if the tree is a bst or not.
    fn is_bst_rec(&self, node_idx: usize, min: u32, max: u32) -> (u32, u32, bool) {
        // Updating main values
        let key = self.nodes[node_idx].key;
        let mut min = if key < min { key } else { min };
        let mut max = if key > max { key } else { max };

        // Visiting left subtree
        if let Some(id_left) = self.nodes[node_idx].id_left {
            let (l_min, l_max, l_bst) = self.is_bst_rec(id_left, min, key - 1);
            if l_max >= key || !l_bst {
                return (0, 0, false);
            }
            min = if l_min < min { l_min } else { min };
        }

        // Visiting right subtree
        if let Some(id_right) = self.nodes[node_idx].id_right {
            let (r_min, r_max, r_bst) = self.is_bst_rec(id_right, key, max);
            if r_min < key || !r_bst {
                return (0, 0, false);
            }
            max = if r_max > max { r_max } else { max };
        }

        // Base Case (we explored the node's subtrees || the node was a leaf)
        (min, max, true)
    }

    /// A public function which determines if the tree calling the method is
    /// a BST or not.
    /// Recall that if a tree is a BST then:
    ///     - max_key(root.left_subtree)  < root.key
    ///     - min_key(root.right_subtree) > root.key
    pub fn is_bst(&self) -> bool {
        let key = self.nodes[0].key;
        let (_, _, res) = self.is_bst_rec(0, key, key);
        res
    }

    /// A private recursive function that calculates for the node at `node_idx`
    /// the maximum path sum from a leaf to another leaf.
    /// # Arguments
    /// 'node_idx' - the index of the current node.
    /// # Returns
    /// * `bu`- max sum path between two leaves in the explored tree.
    /// * `mu`- max sum path from a leaf to the node at `node_idx` (not the final solution,
    ///         but helps upper nodes).
    fn max_path_sum_rec(&self, node_idx: usize) -> (Option<u32>, Option<u32>) {
        // Iteratively checks the left subtree
        let (bl, ml) = match self.nodes[node_idx].id_left {
            None => (None, None),
            Some(id) => self.max_path_sum_rec(id),
        };

        // Iteratively checks the right subtree
        let (br, mr) = match self.nodes[node_idx].id_right {
            None => (None, None),
            Some(id) => self.max_path_sum_rec(id),
        };

        // Determines the maximum path from left_subtree -> current_node -> right_subtree
        // and the maximum path between left_subtree -> current_node and right_subtree -> current_node
        let key = self.nodes[node_idx].key;
        let bu = match (ml, mr) {
            (None, _) => max(bl, br),
            (_, None) => max(bl, br),
            (Some(val_1), Some(val_2)) => max(max(bl, br), Some(val_1 + val_2 + key)),
        };

        let mu: Option<u32> = match max(ml, mr) {
            None => Some(key),
            Some(val) => Some(val + key),
        };

        (bu, mu)
    }

    /// A public function which determines the max_path_sum from a leaf to another leaf
    /// in the tree.
    /// #Returns
    /// The value of the max_path_sum as an Option<u32>. If the value is None, it means
    /// that the max_path_sum does not exists (e.g. there is only one leaf in the tree).
    pub fn max_path_sum(&self) -> Option<u32> {
        let root = 0;
        let (res, _) = self.max_path_sum_rec(root);
        res
    }
}

/// A set of tests for `is_bst` and `is_bst_recursive`.
/// Each test incrementally builds a tree, checking if it's a BST after each node addition.
/// The final tree may or may not be a valid BST, but all intermediate trees are valid BSTs.
/// Each test includes a visual representation of the final tree, with `!<key>!` marking the
/// node that invalidates the BST (if any).
#[cfg(test)]
mod bst_tests {
    use crate::Tree;

    #[test]
    fn bst_1() {
        // [TEST-1] The final tree is a BST:
        //      5
        //    /   \
        //   3     4
        let mut tree = crate::Tree::with_root(5);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (5, 5, true),
            "The tree should be a BST!"
        );

        tree.add_node(0, 3, true);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (3, 5, true),
            "The tree should be a BST!"
        );

        tree.add_node(0, 7, false);
        assert!(tree.is_bst(), "The tree should be a BST!")
    }

    #[test]
    fn bst_2() {
        // [TEST-2] The final tree is NOT a BST. The error is in the left subtree:
        //       5
        //    /    \
        //   3      7
        //    \
        //     !6!    <- 6 shouldn't be > than 5!
        let mut tree = Tree::with_root(5);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (5, 5, true),
            "The tree should be a BST!"
        );

        let left_child = tree.add_node(0, 3, true);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (3, 5, true),
            "The tree should be a BST!"
        );

        tree.add_node(0, 7, false);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (3, 7, true),
            "The tree should be a BST!"
        );

        tree.add_node(left_child, 6, false);
        assert!(!tree.is_bst(), "The tree should NOT be a BST!");
    }

    #[test]
    fn bst_3() {
        // [TEST-3] The final tree is NOT a BST. The error is in the right subtree:
        //      5
        //    /   \
        //   3     7
        //        /
        //       !7!  <-- 7 shouldn't be = than 5!
        let mut tree = Tree::with_root(5);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (5, 5, true),
            "The tree should be a BST!"
        );

        tree.add_node(0, 3, true);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (3, 5, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(0, 7, false);
        assert_eq!(
            tree.is_bst_rec(0, 5, 5),
            (3, 7, true),
            "The tree should be a BST!"
        );

        tree.add_node(right_child, 7, true);
        assert!(!tree.is_bst(), "The tree should NOT be a BST!")
    }

    #[test]
    fn bst_4() {
        // [TEST-4] The final tree is a BST:
        //                       25
        //                /             \
        //               15             30
        //           /       \       /       \
        //          10       20     27       35
        //       /       \         /   \
        //      5        12       26  28
        //    /   \     /   \
        //   3    6    11   13
        let mut tree = Tree::with_root(25);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (25, 25, true),
            "The tree should be a BST!"
        );

        let root = 0;
        let left_child = tree.add_node(root, 15, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (15, 25, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(root, 30, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (15, 30, true),
            "The tree should be a BST!"
        );

        let parent_l = left_child; // 15
        let parent_r = right_child; // 30

        let left_child = tree.add_node(parent_l, 10, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 30, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_l, 20, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 30, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(parent_r, 27, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 30, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 35, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 35, true),
            "The tree should be a BST!"
        );

        let parent_l = left_child; // 10
        let parent_r = right_child; // 27

        let left_child = tree.add_node(parent_l, 5, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(parent_l, 12, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 26, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 28, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        let parent_l = left_child; // 5
        let parent_r = right_child; // 12

        tree.add_node(parent_l, 3, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (3, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_l, 6, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (3, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 11, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (3, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 13, false);
        assert!(tree.is_bst(), "The tree should be a BST!")
    }

    #[test]
    fn bst_5() {
        // [TEST-5] The final tree isn't a BST:
        //                       25
        //                /             \
        //               15             30
        //           /       \       /       \
        //          10       20     27       35
        //       /       \         /   \
        //      5        12       26  28
        //    /   \     /   \
        //   3    6    11   13
        //                    \
        //                    !17!  <-- 17 shouldn't be > 15!
        let mut tree = Tree::with_root(25);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (25, 25, true),
            "The tree should be a BST!"
        );

        let root = 0;
        let left_child = tree.add_node(root, 15, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (15, 25, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(root, 30, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (15, 30, true),
            "The tree should be a BST!"
        );

        let parent_l = left_child; // 15
        let parent_r = right_child; // 30

        let left_child = tree.add_node(parent_l, 10, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 30, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_l, 20, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 30, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(parent_r, 27, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 30, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 35, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (10, 35, true),
            "The tree should be a BST!"
        );

        let parent_l = left_child; // 10
        let parent_r = right_child; // 27

        let left_child = tree.add_node(parent_l, 5, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(parent_l, 12, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 26, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 28, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (5, 35, true),
            "The tree should be a BST!"
        );

        let parent_l = left_child; // 5
        let parent_r = right_child; // 12

        tree.add_node(parent_l, 3, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (3, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_l, 6, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (3, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(parent_r, 11, true);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (3, 35, true),
            "The tree should be a BST!"
        );

        let right_child = tree.add_node(parent_r, 13, false);
        assert_eq!(
            tree.is_bst_rec(0, 25, 25),
            (3, 35, true),
            "The tree should be a BST!"
        );

        tree.add_node(right_child, 17, false);
        assert!(!tree.is_bst(), "The tree should NOT be a BST!")
    }
}

/// A battery of tests for `max_path_sum` and `max_path_sum_rec`.
/// Each test builds a tree step by step, checking `max_path_sum_rec` after each node addition.
/// After the last node, `max_path_sum` is tested on the final tree.
/// A visual representation of the final tree is provided, the nodes marked as `!<key>!`
/// indicates the optimal path.
#[cfg(test)]
mod sum_tests {
    use crate::Tree;

    #[test]
    fn max_sum_1() {
        // The final tree has max_path_sum = None:
        //   1
        let tree = Tree::with_root(1);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(1)));
    }

    #[test]
    fn max_sum_2() {
        // The final tree has max_path_sum = Some(210):
        //          1
        //         /
        //       !10!
        //     /     \
        //  !100!   !100!
        let mut tree = Tree::with_root(1);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(1)));

        let parent = tree.add_node(0, 10, true);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(11)));

        tree.add_node(parent, 100, true);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(111)));

        tree.add_node(parent, 100, false);
        assert_eq!(tree.max_path_sum(), Some(210))
    }

    #[test]
    fn max_sum_3() {
        // The final tree has max_path_sum = Some(202):
        //            1
        //          /   \
        //        !2!    3
        //     /       \
        //  !100!     !100!
        let mut tree = Tree::with_root(1);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(1)));

        let parent = tree.add_node(0, 2, true);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(3)));

        tree.add_node(0, 3, false);
        assert_eq!(tree.max_path_sum_rec(0), (Some(6), Some(4)));

        tree.add_node(parent, 100, true);
        assert_eq!(tree.max_path_sum_rec(0), (Some(106), Some(103)));

        tree.add_node(parent, 100, false);
        assert_eq!(tree.max_path_sum(), Some(202))
    }

    #[test]
    fn max_sum_4() {
        // The final tree has max_path_sum = Some(306):
        //           5
        //         /   \
        //      !1!   !200!
        //    /     \
        //  100   !100!
        let mut tree = Tree::with_root(5);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(5)));

        let parent = tree.add_node(0, 1, true);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(6)));

        tree.add_node(0, 200, false);
        assert_eq!(tree.max_path_sum_rec(0), (Some(206), Some(205)));

        tree.add_node(parent, 100, true);
        assert_eq!(tree.max_path_sum_rec(0), (Some(306), Some(205)));

        tree.add_node(parent, 100, false);
        assert_eq!(tree.max_path_sum(), Some(306))
    }

    #[test]
    fn max_sum_5() {
        // The final tree has max_path_sum = Some(128):
        //            !5!
        //           /   \
        //         !2!     !100!
        //        /   \    /   \
        //      !7!     1  3    !10!
        //     /  \
        //    3   !4!
        let mut tree = Tree::with_root(5);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(5)));

        let left_ch = tree.add_node(0, 2, true);
        assert_eq!(tree.max_path_sum_rec(0), (None, Some(7)));

        let right_ch = tree.add_node(0, 100, false);
        assert_eq!(tree.max_path_sum_rec(0), (Some(107), Some(105)));

        let parent = right_ch;
        tree.add_node(parent, 3, true);
        assert_eq!(tree.max_path_sum_rec(0), (Some(110), Some(108)));

        tree.add_node(parent, 10, false);
        assert_eq!(tree.max_path_sum_rec(0), (Some(117), Some(115)));

        let parent = left_ch;
        tree.add_node(parent, 1, false);
        assert_eq!(tree.max_path_sum_rec(0), (Some(118), Some(115)));

        let parent = tree.add_node(parent, 7, true);
        assert_eq!(tree.max_path_sum_rec(0), (Some(124), Some(115)));

        tree.add_node(parent, 3, true);
        assert_eq!(tree.max_path_sum_rec(0), (Some(127), Some(115)));

        tree.add_node(parent, 4, false);
        assert_eq!(tree.max_path_sum(), Some(128))
    }
}
