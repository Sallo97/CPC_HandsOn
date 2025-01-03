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
// ----------------------------------------------------------------

/// Represents a Matrix, storing all the data in a
/// single Vector. Offers methods to work with the vector
/// using it as a 2D Matrix.
struct CustomMatrix {
    rows: usize,
    cols: usize,
    data: Vec<u8>,
}

impl CustomMatrix {
    /// A Base constructor creating a matrix
    /// in which all values are set to 0
    fn new(rows: usize, cols: usize) -> Self {
        let mut mtx = Self {
            rows: rows,
            cols: cols,
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
    pub fn get_value(&self, i: &usize, j: &usize) -> Option<&u8> {
        self.data.get(self.get_index(i, j))
    }

    /// Set the value at row `i` and col `j` equal to
    /// `val`
    /// Returns the value
    pub fn set_value(&mut self, i: &usize, j: &usize, val: u8) {
        let idx = self.get_index(i, j);
        self.data[idx] = val;
    }
}

/// This function solves PROBLEM #1.
/// Given:
/// - `D` = number of days
/// - `C` = a matrix of size n x D describing the activities
///         available in each city. More formally:
///         ∀i ∈ [1, n].∀j ∈ [1, D].C[i][j] = the number of
///         activities available on the i-th city on the j-th
///         day in a row.
/// Returns the maximum number of activities of a optimal planning
/// over the cities C on D days.
/// In case an error occurs returns `None`
pub fn get_maximum_activities() {}
