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
pub struct ItineraryMatrix {
    rows: usize,
    cols: usize,
    data: Vec<u32>,
}

impl ItineraryMatrix {
    /// A Base constructor creating a matrix
    /// in which all values are set to 0
    pub fn new(rows: usize, cols: usize) -> Self {
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
    pub fn get_value(&self, i: &usize, j: &usize) -> u32 {
        self.data.get(self.get_index(&i, &j)).unwrap().clone()
    }

    /// Set the value at row `i` and col `j` equal to
    /// `val`
    pub fn set_value(&mut self, i: &usize, j: &usize, val: u32) {
        let idx = self.get_index(&i, &j);
        self.data[idx] = val;
    }

    /// Prints the whole matrix
    pub fn print_matrix(&self) {
        for row in 0..self.rows {
            for col in 0..self.cols {
                print!("{} ", self.get_value(&row, &col));
            }
            println!();
        }
    }

    /// given the vector `nums` and an index `row_idx`,
    /// fills the i-th row of the matrix with the elems in `nums`
    pub fn add_row(&mut self, row_idx: usize, nums: &Vec<u32>) {
        for j in 0..nums.len() {
            self.set_value(&row_idx, &j, nums[j]);
        }
    }

    /// Given in input the `mtx` matrix
    /// it returns the matrix `sum` s.t.
    /// ∀i ∈ [0, n-1].∀j ∈ [0, m-1].sum[i][j] = Σ_{k=0 -> j}mtx[i][k]
    fn construct_prefix_sum(&self) -> ItineraryMatrix {
        let mut sum_prefix = ItineraryMatrix::new(self.rows, self.cols);

        for i in 0..self.rows {
            for j in 0..self.cols {
                if j == 0 {
                    sum_prefix.set_value(&i, &j, self.get_value(&i, &j).clone());
                } else {
                    let val = sum_prefix.get_value(&i, &(j - 1)) + self.get_value(&i, &j);
                    sum_prefix.set_value(&i, &j, val);
                }
            }
        }
        sum_prefix
    }

    pub fn find_max_activities(&self) -> u32 {
        // Construct prefix sum matrix
        let sum = self.construct_prefix_sum();

        // Construct solution matrix
        let mut dp = ItineraryMatrix::new(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                // max {left; right}
                // left = dp(i-1, j)
                // right = max_(0<= z <= j) dp(i-1, j - (z + 1)) + sum(i,z)
                let left = if i > 0 { dp.get_value(&(i - 1), &j) } else { 0 };

                // Find the maximum
                let rigth = (0..=j)
                    .map(|z| {
                        let days = z + 1;
                        let sum_values = sum.get_value(&i, &z);
                        if i > 0 && j >= days {
                            sum_values + dp.get_value(&(i - 1), &(j - days))
                        } else {
                            sum_values
                        }
                    })
                    .max()
                    .unwrap_or(0);

                // Store the final value
                dp.set_value(&i, &j, cmp::max(left, rigth));
            }
        }
        dp.get_value(&(self.rows - 1), &(self.cols - 1)).clone()
    }
}
