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

    /// A private recursive function that determines if the sub-tree
    /// starting at the node with index `node_idx` is a BST.
    /// # Arguments
    /// * `node_idx` - the idx in the tree containing the current node.
    /// * `min`  - the current minimum for which `node.key` > `min`
    /// * `max`  - the current maximum for which `node.key` < `max`
    fn is_bst_rec(&self, node_idx: usize, min: &mut u32, max: &mut u32) -> (u32, u32, bool) {
        // Updating main values
        let key = self.nodes[node_idx].key;
        if key < *min {
            *min = key;
        }
        if key > *max {
            *max = key;
        }

        // Visiting left sub-tree
        if let Some(id_left) = self.nodes[node_idx].id_left {
            *max = key;
            let (l_min, l_max, l_bool) = self.is_bst_rec(id_left, min, max);
            if l_max > key || !l_bool {
                return (0, 0, false);
            }
            if l_min < *min {
                *min = l_min;
            }
        }

        // Visiting right sub-tree
        if let Some(id_right) = self.nodes[node_idx].id_right {
            *min = key;
            let (r_min, r_max, r_bool) = self.is_bst_rec(id_right, min, max);
            if r_min < key || !r_bool {
                return (0, 0, false);
            }
            if r_max > *max {
                *max = r_max;
            }
        }

        // Base Case (node is a Leaf or we visited its subtree(s))
        (*min, *max, true)
    }

    /// A dummy public function returns a boolean s.t.:
    /// true -> the tree is a BST
    /// false -> otherwise
    /// # Arguments
    /// # Hints
    /// Recall that idx_of_root = 0
    pub fn is_bst(&self) -> bool {
        let mut key = self.nodes[0].key;
        let max: &mut u32 = &mut (key + 1);
        let min: &mut u32 = &mut key;
        let (_, _, res) = self.is_bst_rec(0, min, max);
        res
    }

    /// A private recursive function that determines for the given node
    /// the pair of the best sum_path so far and the max_path so far s.t
    /// sum_path = contains the best path, that is if we need to follow the left
    ///             or right subtree of the current node
    /// max_path = contains the value of summing of the path from
    ///             left_leaf -> current node -> right_leaf
    /// # Arguments
    /// 'node_idx' - the idx in the tree containing the current node.
    fn max_path_sum_rec(&self, node_idx: usize) -> (Option<u32>, Option<u32>) {
        // Iterative Case = the current node has at least a child
        let (bl, ml) = match self.nodes[node_idx].id_left {
            None => (None, None),
            Some(id) => self.max_path_sum_rec(id),
        };

        let (br, mr) = match self.nodes[node_idx].id_right {
            None => (None, None),
            Some(id) => self.max_path_sum_rec(id),
        };

        let key = self.nodes[node_idx].key;
        let current_subtree_sum = match (ml, mr) {
            (None, _) => None,
            (_, None) => None,
            (Some(val_1), Some(val_2)) => Some(val_1 + val_2 + key),
        };
        let bu = max(max(bl, br), current_subtree_sum);

        let mu: Option<u32> = match max(ml, mr) {
            None => Some(key),
            Some(val) => Some(val + key),
        };

        (bu, mu)
    }

    /// A dummy public function that returns the maximum path sum
    pub fn max_path_sum(&self) -> (Option<u32>, Option<u32>) {
        let root = 0;
        self.max_path_sum_rec(root)
    }
}

/// This is a battery of tests for the is_bst and is_bst_recursive function.
/// Each test consists in constructing a tree step by step.
/// Each time we add a new node, we test if the tree is a BST.
/// The final constructed tree could be a BST or not a BST, all the intermediate trees are BST.
/// In each test there is a comment giving a visual representation the final tree.
/// With !<key>! we indicate the node that makes the BST invalid.
#[cfg(test)]
mod bst_tests {

    use super::*;

    #[test]
    fn bst_1() {
        // [TEST-1] The final tree is a BST:
        //      5
        //    /   \
        //   3     7
        let mut tree = Tree::with_root(5);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(0, 3, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(0, 7, false);
        assert!(tree.is_bst(), "The tree should be a BST!");
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
        assert!(tree.is_bst(), "The tree should be a BST!");

        let left_child = tree.add_node(0, 3, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(0, 7, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

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
        //       !4!  <-- 4 shouldn't be < than 5!
        let mut tree = Tree::with_root(5);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(0, 3, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(0, 7, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(right_child, 4, true);
        assert!(!tree.is_bst(), "The tree should NOT be a BST!");
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
        assert!(tree.is_bst(), "The tree should be a BST!");

        let root = 0;
        let left_child = tree.add_node(root, 15, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(root, 30, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let parent_l = left_child; // 15
        let parent_r = right_child; // 30

        let left_child = tree.add_node(parent_l, 10, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_l, 20, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(parent_r, 27, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_r, 35, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let parent_l = left_child; // 10
        let parent_r = right_child; // 27

        let left_child = tree.add_node(parent_l, 5, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(parent_l, 12, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_r, 26, true);
        tree.add_node(parent_r, 28, false);

        let parent_l = left_child; // 5
        let parent_r = right_child; // 12

        tree.add_node(parent_l, 3, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_l, 6, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_r, 11, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_r, 13, false);
        assert!(tree.is_bst(), "The tree should be a BST!");
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
        assert!(tree.is_bst(), "The tree should be a BST!");

        let root = 0;
        let left_child = tree.add_node(root, 15, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(root, 30, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let parent_l = left_child; // 15
        let parent_r = right_child; // 30

        let left_child = tree.add_node(parent_l, 10, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_l, 20, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(parent_r, 27, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_r, 35, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let parent_l = left_child; // 10
        let parent_r = right_child; // 27

        let left_child = tree.add_node(parent_l, 5, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(parent_l, 12, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_r, 26, true);
        tree.add_node(parent_r, 28, false);

        let parent_l = left_child; // 5
        let parent_r = right_child; // 12

        tree.add_node(parent_l, 3, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_l, 6, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(parent_r, 11, true);
        assert!(tree.is_bst(), "The tree should be a BST!");

        let right_child = tree.add_node(parent_r, 13, false);
        assert!(tree.is_bst(), "The tree should be a BST!");

        tree.add_node(right_child, 17, false);
        assert!(!tree.is_bst(), "The tree should NOT be a BST!");
    }

    #[test]
    fn bst_6() {
        // TODO add a positive case here!
    }
}

/// This is a battery of tests for the max_path_sum and max_path_sum_rec methods.
/// Each test consists in returning the final pair (bu, mu) relative to the whole tree.
/// For each test we give a visual representation of the tree.
/// nodes marked as !<key>! specify that they are in the optimal path
#[cfg(test)]
mod sum_tests {
    use crate::Tree;

    #[test]
    fn max_sum_1() {
        // The method should return (128, 115):
        //            !5!
        //           /   \
        //         !2!     !100!
        //        /   \    /   \
        //      !7!     1  3    !10!
        //     /  \
        //    3   !4!
        let mut tree = Tree::with_root(5);
        assert_eq!(tree.max_path_sum(), (None, Some(5)));

        let left_ch = tree.add_node(0, 2, true);
        assert_eq!(tree.max_path_sum(), (None, Some(7)));

        let right_ch = tree.add_node(0, 100, false);
        assert_eq!(tree.max_path_sum(), (Some(107), Some(105)));

        let parent = right_ch;
        tree.add_node(parent, 3, true);
        assert_eq!(tree.max_path_sum(), (Some(110), Some(108)));

        tree.add_node(parent, 10, false);
        assert_eq!(tree.max_path_sum(), (Some(117), Some(115)));

        let parent = left_ch;
        tree.add_node(parent, 1, false);
        assert_eq!(tree.max_path_sum(), (Some(118), Some(115)));

        let parent = tree.add_node(parent, 7, true);
        assert_eq!(tree.max_path_sum(), (Some(124), Some(115)));

        tree.add_node(parent, 3, true);
        assert_eq!(tree.max_path_sum(), (Some(127), Some(115)));

        tree.add_node(parent, 4, false);
        assert_eq!(tree.max_path_sum(), (Some(128), Some(115)));
    }

    #[test]
    fn max_sum_2() {
        // The method should return (128, 115):
        //            1
        //          /   \
        //        !2!    3
        //     /       \
        //  !100!     !100!
        let mut tree = Tree::with_root(1);
        assert_eq!(tree.max_path_sum(), (None, Some(1)));

        let parent = tree.add_node(0, 2, true);
        assert_eq!(tree.max_path_sum(), (None, Some(3)));

        tree.add_node(0, 3, false);
        assert_eq!(tree.max_path_sum(), (Some(6), Some(4)));

        tree.add_node(parent, 100, true);
        assert_eq!(tree.max_path_sum(), (Some(106), Some(103)));

        tree.add_node(parent, 100, false);
        assert_eq!(tree.max_path_sum(), (Some(202), Some(103)));
    }
}
