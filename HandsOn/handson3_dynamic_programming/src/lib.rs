/// This code implements the solutions for the third HandsOn of
/// the course "Competitive Programming and Contest" 2024/25
/// course held at at the University of Pisa.
///
/// [PROBLEM #1 - Holiday Planning]
/// You are given a number of days `D` and a set of cities to visit:
/// `C = {(a1,1, ..., a1,D); ..., (an,1, ..., an,D)}` where:
/// - `a_i,j` represents the number of activities you can do in the
/// `i`-th city on the `j`-th consecutive day you spend in that city.
/// The task is to find the maximum number of activities possible in
/// `D` days, visiting some of the available cities.
/// Note:
/// - Cities are visited sequentially from left to right.
/// - You can choose to skip a city entirely.
/// - Once you leave a city, you cannot return to it.
///
/// [PROBLEM #2 - Design a Course]
/// You are given a set of `n` topics, where each topic is represented
/// by a tuple of two `u32` values:
/// - The first element represents the topic's *beauty* (`bi`).
/// - The second element represents the topic's *difficulty* (`di`).
/// The task is to design a course as a sequence of topics such that:
/// 1. If a topic `t_i` with parameters `(b_i, d_i)` is included in the
/// course, then the next topic `t_j` (where `j > i`) must satisfy:
///    - `b_j > b_i` (the beauty of the next topic is strictly greater
///       than the current topic).
///    - `d_j > d_i` (the difficulty of the next topic is strictly greater
///       than the current topic).
/// The goal is to find the maximum length of such a sequence of topics in
/// `O(n log n)` time.
use std::cmp;

/// The itinerary is interpreted as a fixed-size matrix.
/// In practice, it is represented as a `Vec<u32>` and methods are provided
/// to abstract it for the user as if it were a real matrix.
pub struct ItineraryMatrix {
    rows: usize,
    cols: usize,
    data: Vec<u32>,
}

impl ItineraryMatrix {
    /// Creates a new matrix with the specified number of `rows` and `cols`,
    /// where all elements are initialized to 0.
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

    /// Computes the linear index corresponding to the cell at row `i` and column `j`
    /// in the matrix.
    fn get_index(&self, i: &usize, j: &usize) -> usize {
        (i * self.cols) + j
    }

    /// Retrieves the value stored at the cell located at row `i` and column `j`.
    pub fn get_value(&self, i: &usize, j: &usize) -> u32 {
        self.data.get(self.get_index(&i, &j)).unwrap().clone()
    }

    /// Sets the value of the cell located at row `i` and column `j` to the specified `val`.
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

    /// Fills the specified row of the matrix with the elements from the given vector `nums`.
    pub fn add_row(&mut self, row_idx: usize, nums: &Vec<u32>) {
        for j in 0..nums.len() {
            self.set_value(&row_idx, &j, nums[j]);
        }
    }

    /// Constructs a prefix sum matrix `sum` for the caller matrix.
    /// ∀i ∈ \[0, n-1].∀j ∈ \[0, m-1].`sum[i][j]` = Σ_{k=0 to j} self\[i]\[k]
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

    /// Calculates the maximum number of activities that can be completed
    /// in the given itinerary, following a set of rules:
    /// - Cities must be visited sequentially from left to right (no backtracking).
    /// - A city can be skipped entirely.
    /// - Once a city is left, it cannot be revisited.
    ///
    /// This problem is solved using Dynamic Programming (DP), where a 2D matrix `dp` is constructed.
    /// The matrix `dp[i][j]` represents the maximum number of activities that can be completed
    /// when considering the first `i` cities and `j` available days.
    ///
    /// The value of `dp[i][j]` is computed as the maximum of two choices:
    /// - **`dp[i-1][j]`**: The maximum activities up to the previous city with the same number of days available.
    /// - **`max_{0 <= z <= j} (dp[i-1][j - (z + 1)] + sum[i][z])`**: The maximum number of activities achievable
    ///   by spending `z` days at city `i`, where `sum[i][z]` is the prefix sum of activities in city `i` for up to `z` days.
    ///
    /// The final solution is stored in `dp[rows-1][cols-1]`.
    ///
    /// # Time Complexity:
    /// The function costs `O(n * d * d)` time where:
    /// - `n` is the number of cities in the itinerary (`rows` in the matrix)
    /// - `d` is the number of available days (`cols` in the matrix).
    ///
    /// The complexity arises from the size of the solution matrix `dp` which has size n * d and the
    /// cost for computing each cell `dp[i][j]`: for determining it we need to iterate through all possible values,
    /// of `z`, costing O(d) time.

    pub fn find_max_activities(&self) -> u32 {
        // Construct prefix sum matrix
        let sum = self.construct_prefix_sum();

        // Construct solution matrix
        let mut dp = ItineraryMatrix::new(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                // left = dp(i-1, j)
                let left = if i > 0 { dp.get_value(&(i - 1), &j) } else { 0 };

                // right = max_(0<= z <= j) dp(i-1, j - (z + 1)) + sum(i,z)
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

                // d[i][j] = max {left; right}
                dp.set_value(&i, &j, cmp::max(left, rigth));
            }
        }

        dp.get_value(&(self.rows - 1), &(self.cols - 1)).clone()
    }
}

/// Represents a Topic, described by:
/// - `beauty`: A u32 value indicating the appeal of the topic.
/// - `difficulty`: A u32 value indicating the complexity of the topic.
struct Topic {
    beauty: u32,
    difficulty: u32,
}

/// The list of topics is interpreted as a fixed-size `Vec<Topic>`.
pub struct TopicList {
    num_of_topics: usize,
    data: Vec<Topic>,
}

impl TopicList {
    /// Constructs a new `TopicList` containing `n` topics,
    /// each with both `beauty` and `difficulty` set to 0.
    pub fn new(num_of_topics: usize) -> Self {
        let mut lst = Self {
            num_of_topics,
            data: Vec::with_capacity(num_of_topics),
        };
        for _ in 0..(num_of_topics) {
            lst.data.push(Topic {
                beauty: 0,
                difficulty: 0,
            });
        }
        lst
    }

    /// Updates the topic at the specified index in the list with new `beauty` and `difficulty` values.
    pub fn set_topic(&mut self, idx: usize, beauty: u32, difficulty: u32) {
        let new_t = Topic { beauty, difficulty };
        self.data[idx] = new_t;
    }

    /// Returns the length of the maximum course.
    /// A course is a subsequence of topics that satisfies the following conditions:
    /// - The topics must be ordered such that each subsequent topic has both a strictly
    ///   greater beauty and a strictly greater difficulty than the previous one.
    ///
    /// The problem is solved by first sorting the list of topics based on their
    /// `difficulty` (increasing order) and, in case of ties, by `beauty` (increasing order).
    /// After sorting, the function finds the length of the longest subsequence where the
    /// topics' `beauty` values form an increasing sequence.
    ///
    /// # Time Complexity:
    /// The function runs in O(n log n) time, where `n` is the number of topics in the list.
    /// The time complexity comes from the sorting step `O(n log n)` and the subsequent
    /// binary search for the longest increasing subsequence of beauty values which are n and
    /// each costs `O(log n)`.
    pub fn find_max_course(&mut self) -> usize {
        // Sort the list in increasing order by their difficulty key
        // If two entries t1 and t2 have the same key, I order them
        // according to their beauty
        self.data.sort_by(|t1, t2| {
            t1.difficulty
                .cmp(&t2.difficulty)
                .then_with(|| t1.beauty.cmp(&t2.beauty))
        });

        // Removes entries with same difficulty key, keeping
        // the one with smaller beauty
        self.data.dedup_by_key(|t| t.difficulty);

        // Construct d
        let mut d: Vec<Option<u32>> = vec![None; self.num_of_topics];

        let mut max_pos = 0;
        // Filling d
        for topic in &self.data {
            let pos = d
                .binary_search_by(|val| match val {
                    Some(x) => {
                        if x < &topic.beauty {
                            std::cmp::Ordering::Less
                        } else {
                            std::cmp::Ordering::Greater
                        }
                    }
                    None => std::cmp::Ordering::Greater,
                })
                .unwrap_or_else(|index| index);

            d[pos] = Some(topic.beauty);
            max_pos = cmp::max(max_pos, pos);
        }

        max_pos + 1
    }

    /// Prints the whole list
    pub fn print_list(&self) {
        println!("[BEAUTY]\t[DIFFICULTY]");
        for topic in &self.data {
            println!("{}\t{}", topic.beauty, topic.difficulty);
        }
    }
}
