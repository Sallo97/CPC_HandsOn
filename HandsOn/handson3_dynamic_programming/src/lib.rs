/// This code implements the solutions for the third HandsOn of
/// the course "Competitive Programming and Contest" 2024/25
/// course held at at the University of Pisa.
///
/// [PROBLEM #1 - Holiday Planning]
/// Given a number of days D and a set of cities to visit
/// C = {(a1,1 , ... , a1,D); ... ; (an,1, ... , an,D)}
/// s.t ai,j = the number of activities you can do in the
/// i-th city on the j-th day in a row you are in that city,
/// find the maximum  number of activities possible to do in
/// D days visiting some of the available cities.
/// The cities are visited from left-to-right, its possible to
/// skip entirely a city and once you decide to leave a city you
/// cannot return to it ever again.
///
/// [PROBLEM #2 - TODO]
///
use std::cmp;

/// Represents a fixed size Matrix.
pub struct CustomMatrix {
    rows: usize,
    cols: usize,
    data: Vec<u32>,
}

impl CustomMatrix {
    /// A Base constructor creating a matrix
    /// in which all values are set to 0
    fn new(rows: usize, cols: usize) -> Self {
        let mut mtx = Self {
            rows,
            cols,
            data: Vec::with_capacity(rows * cols),
        };
        let length = rows * cols;
        for _ in 0..(length) {
            mtx.data.push(0);
        }
        mtx
    }

    /// Returns the real index where cell `[i][j]`
    /// is stored.
    fn get_index(&self, i: &usize, j: &usize) -> usize {
        (i * self.cols) + j
    }

    /// Returns the value at row `i` and col `j`
    /// if i < 0 or j < 0 returns 0
    pub fn get_value(&self, i: &usize, j: &usize) -> &u32 {
        self.data.get(self.get_index(&i, &j)).unwrap()
    }

    /// Set the value at row `i` and col `j` equal to
    /// `val`
    pub fn set_value(&mut self, i: &usize, j: &usize, val: u32) {
        let idx = self.get_index(&i, &j);
        self.data[idx] = val;
    }
}

/// Given in input the `mtx` matrix
/// it returns the matrix `sum` s.t.
/// ∀i ∈ [0, n-1].∀j ∈ [0, m-1].sum[i][j] = Σ_{k=0 -> j}mtx[i][k]
fn construct_prefix_sum(mtx: &CustomMatrix) -> CustomMatrix {
    let mut sum_prefix = CustomMatrix::new(mtx.rows, mtx.cols);

    for i in 0..mtx.rows {
        for j in 0..mtx.cols {
            if j == 0 {
                sum_prefix.set_value(&i, &j, mtx.get_value(&i, &j).clone());
            } else {
                let val = sum_prefix.get_value(&i, &(j - 1)) + mtx.get_value(&i, &j);
                sum_prefix.set_value(&i, &j, val);
            }
        }
    }
    sum_prefix
}

#[cfg(test)]
mod prefix_sum_tests {
    use crate::{construct_prefix_sum, CustomMatrix};

    #[test]
    fn psum_1() {
        // Input mtx:
        // 3 2 1
        // 3 1 1
        // Output sum prefix:
        // 3 5 6
        // 3 4 5

        // Constructing input mtx
        let mut mtx = CustomMatrix::new(2, 3);
        mtx.set_value(&0, &0, 3);
        mtx.set_value(&0, &1, 2);
        mtx.set_value(&0, &2, 1);

        mtx.set_value(&1, &0, 3);
        mtx.set_value(&1, &1, 1);
        mtx.set_value(&1, &2, 1);

        // Testing result
        let sum = construct_prefix_sum(&mtx);
        assert_eq!(sum.get_value(&0, &0), &3);
        assert_eq!(sum.get_value(&0, &1), &5);
        assert_eq!(sum.get_value(&0, &2), &6);

        assert_eq!(sum.get_value(&1, &0), &3);
        assert_eq!(sum.get_value(&1, &1), &4);
        assert_eq!(sum.get_value(&1, &2), &5);
    }

    #[test]
    fn psum_2() {
        // Input mtx:
        // 100 100 1
        // 1   1   2000
        // Output sum prefix:
        // 100 200 201
        // 100 200 2002

        // Contructing input mtx
        let mut mtx = CustomMatrix::new(2, 3);
        mtx.set_value(&0, &0, 100);
        mtx.set_value(&0, &1, 100);
        mtx.set_value(&0, &2, 1);

        mtx.set_value(&1, &0, 1);
        mtx.set_value(&1, &1, 1);
        mtx.set_value(&1, &2, 2000);

        // Testing result
        let sum = construct_prefix_sum(&mtx);
        assert_eq!(sum.get_value(&0, &0), &100);
        assert_eq!(sum.get_value(&0, &1), &200);
        assert_eq!(sum.get_value(&0, &2), &201);

        assert_eq!(sum.get_value(&1, &0), &1);
        assert_eq!(sum.get_value(&1, &1), &2);
        assert_eq!(sum.get_value(&1, &2), &2002);
    }
}
