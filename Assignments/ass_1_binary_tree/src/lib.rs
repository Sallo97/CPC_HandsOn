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

    /// A private recursive function that determines if the given tree
    /// starting ad node `node` is a BST.
    /// # Arguments
    /// * `node_idx` - the idx in the tree containing the current node.
    /// * `tree` - the data structure representing the tree.
    /// * `min`  - the current minimum for which `node.key` > `min`
    /// * `max`  - the current maximum for which `node.key` < `max`
    fn is_bst_rec(&self, node_idx: usize, min_key: u32, max_key: u32) -> bool {
        let key = self.nodes[node_idx].key;

        if (min_key <= key) && (key < max_key) {
            if let Some(id_left) = self.nodes[node_idx].id_left {
                if !self.is_bst_rec(id_left, self.nodes[id_left].key, key) {
                    return false;
                }
            }
            if let Some(id_right) = self.nodes[node_idx].id_right {
                if !self.is_bst_rec(id_right, key, self.nodes[id_right].key + 1) {
                    return false;
                }
            }

            true
        } else {
            false
        }
    }

    /// A dummy public function that given a tree, returns a boolean s.t.:
    /// true -> the given tree is a BST
    /// false -> otherwise
    /// # Arguments
    /// * `tree` - the data structure representing the tree
    /// # Hints
    /// Recall that idx_of_root = 0
    pub fn is_bst(&self) -> bool {
        let key = self.nodes[0].key;
        self.is_bst_rec(0, key, key + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bst_test_1() {
        // [TEST-1] We will construct the tree step by step, testing it each time we add a new node.
        // The tree should be a BST until the last insertion when we add the node 9.
        //            25
        //          /     \
        //          15     30
        //       /     \
        //       10     20
        //     /    \
        //    5      13
        //   / \     /
        //  3   4   !9! <- here is the error!
        let mut tree = Tree::with_root(25);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        let left_child = tree.add_node(0, 15, true);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        let right_child = tree.add_node(0, 30, false);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        let right_child = tree.add_node(left_child, 20, false);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        let left_child = tree.add_node(left_child, 10, true);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        let parent = left_child;
        let left_child = tree.add_node(parent, 5, true);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        tree.add_node(left_child, 3, true);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        tree.add_node(left_child, 6, false);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        let right_child = tree.add_node(parent, 13, false);
        assert_eq!(tree.is_bst(), true, "The tree should be a BST!");

        tree.add_node(right_child, 9, true); //LAST NODE TO ADD!!!!! HERE IS THE ERROR TO CHECK!
        assert_eq!(tree.is_bst(), false, "The tree should NOT be a BST!");
    }
}
