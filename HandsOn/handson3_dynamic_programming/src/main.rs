use handson3_dynamic_programming::{ItineraryMatrix, TopicList};
use std::fs::File;
use std::io::{self, BufRead};
use std::usize;

/// This program checks the correctness of the implemented solutions
/// for the third HandsOn from the "Competitive Programming and Contests"
/// 2024/25 course held at the University of Pisa.
///
/// This code tests the solutions to the two assigned problems:
/// - `Holiday Planning`
/// - `Design a course`,
/// using the test sets provided.
/// The program assumes that the tests are stored in the folders "Testset_handson3_p1"
/// and "Testset_handson3_p2" at the root of the cargo project.
fn main() {
    let tests = vec![5, 11];
    for i in 1..=2 {
        println!("{}", "Testing Problem #$".replace("$", &i.to_string()));
        for j in 0..tests[i - 1] {
            let files = get_files(i, j);
            let res = match i {
                1 => holiday_planning(files.0, files.1),
                _ => design_a_course(files.0, files.1),
            };
            print_test_result(res, j);
        }
    }
}

/// Executes the `Holiday Planning` problem for a given pair
/// of test files `(input, output)`.
/// Returns `true` if the generated output matches the
/// expected `output`, `false` otherwise.
fn design_a_course(input: File, output: File) -> bool {
    // Construct the input List
    let mut topic_list = construct_topic_list(input);
    let my_res = topic_list.find_max_course();

    // Compare result with expected one
    let exp_res: usize = io::BufReader::new(output)
        .lines()
        .next()
        .expect("Error")
        .unwrap()
        .trim()
        .parse()
        .unwrap();

    exp_res == my_res
}

/// Given the `input` test file constructs the associated topics list and returns it.
fn construct_topic_list(input: File) -> TopicList {
    // Creating the iterator for scanning the file
    let input = io::BufReader::new(input);
    let mut input = input.lines();

    // Determining the number of topics n
    let n: usize = input
        .next()
        .expect("Error")
        .unwrap()
        .trim()
        .parse()
        .unwrap();

    // Constructing list
    let mut lst = TopicList::new(n);

    // Filling list
    for (index, line) in input.enumerate() {
        let b_d: Vec<u32> = line
            .unwrap()
            .split_whitespace()
            .map(|word| word.parse().unwrap())
            .collect();
        if b_d.len() > 0 {
            let (beauty, difficulty) = (b_d[0], b_d[1]);
            lst.set_topic(index, beauty, difficulty);
        }
    }

    lst
}

/// Prints the message "Test i - Passed" or "Test i - Failed"
/// based on the outcome of the `i`-th test.
fn print_test_result(b: bool, i: usize) {
    let base_success = "Test $ - Passed";
    let base_fail = "Test $ - Failed";
    if b {
        let msg = base_success.replace("$", &i.to_string());
        println!("{msg}");
    } else {
        let msg = base_fail.replace("$", &i.to_string());
        println!("{msg}");
    }
}

/// Returns the test pair (input,output) for the
/// `j`-th test file of the `i`-th problem
fn get_files(i: usize, j: usize) -> (File, File) {
    let base_in = "./Testset_handson3_p*/input$.txt";
    let base_out = "./Testset_handson3_p*/output$.txt";
    let input = base_in
        .replace("*", &i.to_string())
        .replace("$", &j.to_string());
    let output = base_out
        .replace("*", &i.to_string())
        .replace("$", &j.to_string());
    let input = File::open(&input).unwrap();
    let output = File::open(&output).unwrap();
    (input, output)
}

/// Executes the `Holiday Planning` problem for a given pair
/// of test files `(input, output)`.
/// Returns `true` if the generated output matches the
/// expected `output`, `false` otherwise.
fn holiday_planning(input: File, output: File) -> bool {
    // Constructing the input matrix
    let itinerary = construct_itinerary(input);
    let my_res = itinerary.find_max_activities();

    // Getting the expected result from output
    let exp_res: u32 = io::BufReader::new(output)
        .lines()
        .next()
        .unwrap()
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    exp_res == my_res
}

/// Given the `input` test file constructs the associated itinerary and returns it.
fn construct_itinerary(input: File) -> ItineraryMatrix {
    // Creating the iterator for scanning the file
    let input = io::BufReader::new(input);
    let mut input = input.lines();

    // Determining n and d
    let n_d: Vec<usize> = input
        .next()
        .expect("Error")
        .unwrap()
        .split_whitespace()
        .map(|word| word.parse().unwrap())
        .collect();
    let (n, d) = (n_d[0], n_d[1]);

    // Parsing matrix
    let mut mtx = ItineraryMatrix::new(n, d);
    for (index, line) in input.enumerate() {
        let numbers: Vec<u32> = line
            .unwrap()
            .split_whitespace()
            .map(|word| word.parse().unwrap())
            .collect();
        mtx.add_row(index, &numbers);
    }
    mtx
}
