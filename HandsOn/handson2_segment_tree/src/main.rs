use handson2_segment_tree::FreqSTree;
use handson2_segment_tree::MaxSTree;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::ptr::read;

fn main() {
    let base_success = "Test $ - Passed";
    let base_fail = "Test $ - Failed";

    // Executing Problem #1
    println!("Testing Problem #1 - MinMax");
    for i in 0..11 {
        let files = get_next_files(1, i);
        let res = min_max(files.0, files.1);
        if res {
            let msg = base_success.replace("$", &i.to_string());
            println!("{msg}");
        } else {
            let msg = base_fail.replace("$", &i.to_string());
            println!("{msg}");
        }
    }

    // Executing Problem #2
    println!("Testing Problem #1 - IsThere");
    for i in 0..8 {
        let files = get_next_files(1, i);
    }
}

fn get_next_files(i: usize, j: usize) -> (File, File) {
    let base_in = "./tests/problem_*/input/input$.txt";
    let base_out = "./tests/problem_*/output/output$.txt";
    let input = base_in.replace("*", &i.to_string());
    let output = base_out.replace("*", &i.to_string());
    let input = input.replace("$", &j.to_string());
    let output = output.replace("$", &j.to_string());
    let input = File::open(&input).unwrap();
    let output = File::open(&output).unwrap();
    (input, output)
}

/// Execute the min_max problem
/// for a given pair `(input, output)` test files
/// Returns true if the produced outputs follows
/// the test `output`, false otherwise
fn min_max(input: File, output: File) -> bool {
    // Creating the iterator for scanning the file
    let input = io::BufReader::new(input);
    let mut input = input.lines();

    // Determining n and m
    let n_m = input.next().unwrap().unwrap();
    let n_m = get_inputs(Some(2), n_m).unwrap();

    let (n, m) = (n_m[0], n_m[1]);

    // Determing a
    let a = input.next().unwrap().unwrap();
    let a = get_inputs(Some(n), a);
    let a = a.unwrap();

    // Construct the tree
    let tree = MaxSTree::new(&a);
    let mut tree = tree.unwrap();

    // Store results of max query in `res`
    let mut res: Vec<usize> = Vec::new();

    // Execute m queries from file
    for i in 0..m {
        let q = input.next().unwrap().unwrap();
        let q = get_inputs(None, q);

        if let Some(vec) = q {
            match vec[0] {
                0 => tree.update((vec[1], vec[2]), vec[3]),
                _ => {
                    if let Some(val) = tree.max((vec[1], vec[2])) {
                        res.push(val);
                    }
                }
            }
        }
    }

    // Checking that the results are equal to the ones in output
    let output = io::BufReader::new(output);
    let mut output = output.lines();
    for item in res {
        let to_check = output.next().unwrap().unwrap();
        let to_check: usize = to_check.parse().unwrap();
        if item != to_check {
            return false;
        }
    }
    true
}

/// Gets an input line from standard input
/// and returns a `Vec<usize>` of `n` elems
/// If n = None it means we are getting a query for
/// min_max. After getting the input it will read
/// the first element in the parsed vector and
/// if vec[0] = 0 -> Update Query vec.len() == 4
/// if vec[0] = 1 -> Update Query vec.len() == 3
/// otherwise return None
fn get_inputs(n: Option<usize>, str: String) -> Option<Vec<usize>> {
    let inputs: Vec<&str> = str.trim().split_whitespace().collect();

    // Detemining n
    let n = if let Some(val) = n {
        Some(val)
    } else {
        let val: usize = inputs[0].parse().unwrap();
        match val {
            0 => Some(4),
            1 => Some(3),
            _ => None,
        }
    };

    // Convert inputs into a vector of uints
    if Some(inputs.len()) == n {
        let ret = inputs.iter().map(|s| s.parse::<usize>()).collect();
        match ret {
            Ok(ret) => Some(ret),
            Err(_) => {
                eprintln!("Error while parsing the input");
                None
            }
        }
    } else {
        eprintln!("Gotten a string with more elems than requested");
        None
    }
}
