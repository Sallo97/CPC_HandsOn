// This code is an implementation of the Segment Tree providing a solution
// to the two problems given for the 2nd HandsOn of Competitive Programming and Contest
// at the University of Pisa (24/25)
//
// [FIRST-PROBLEM] [STATUS = Incomplete]
// You are given an array A[1,n] of n positive integers, each integer is at most n.
// You have to build a data structure to answer two different types of queries:
// - Update(i,j,T): ∀ k in [1,n].A[k] = min(A[k], T)
// - Max(i, j) that returns the largest value in A[i...j]
//
// [SECOND-PROBLEM] [STATUS = on the high sea]

use std::cmp;

pub struct STNode {
    key: usize,
    children: (Option<usize>, Option<usize>),
    range: (usize, usize),
}

impl STNode {
    // TODO Add comments
    // - a: the array containing the values to index
    // - idx: the index of the element in the array we want to put
    //        in the leaf
    fn new_leaf(a: Vec<usize>, idx: usize) -> Self {
        Self {
            key: a[idx],
            children: (None, None),
            range: (idx, idx),
        }
    }

    // TODO Add comment
    fn new_node(
        key: usize,
        children: (Option<usize>, Option<usize>),
        range: (usize, usize),
    ) -> Self {
        Self {
            key,
            children,
            range,
        }
    }
}
