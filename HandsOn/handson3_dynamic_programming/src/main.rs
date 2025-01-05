use handson3_dynamic_programming::find_max_activities;
use handson3_dynamic_programming::CustomMatrix;
use std::fs::File;
use std::io::{self, BufRead};
use std::usize;

/// This program checks the correctness of the implemented solutions
/// for the second HandsOn from the "Competitive Programming and Contests"
/// 2024/25 course held at the University of Pisa.
/// This code tests the solutions to the two assigned problems, `Holiday Planning` and `???`,
/// using the test sets provided.
/// The program assumes that the tests are stored in the folders "Testset_handson3_p1"
/// and "Testset_handson3_p2" at the root of the cargo project.
fn main() {
    let tests = vec![5, 0];
    for i in 1..=2 {
        println!("{}", "Testing Problem #$".replace("$", &i.to_string()));
        for j in 0..tests[i - 1] {
            let files = get_files(i, j);
            let res = match i {
                1 => holiday_planning(files.0, files.1),
                _ => todo(),
            };
            print_test_result(res, j);
        }
    }
}

fn todo() -> bool {
    true
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
    let my_res = find_max_activities(&itinerary);

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

/// Gotten the `input` test file constructs the associated matrix
fn construct_itinerary(input: File) -> CustomMatrix {
    // Creating the iterator for scanning the file
    let input = io::BufReader::new(input);
    let mut input = input.lines();

    // Determining n and d
    let n_d: Vec<usize> = input
        .next()
        .expect("Error")
        .unwrap()
        .split_whitespace()
        .map(|word| word.parse::<usize>().unwrap())
        .collect();
    let (n, d) = (n_d[0], n_d[1]);

    // Parsing matrix
    let mut mtx = CustomMatrix::new(n, d);
    for (index, line) in input.enumerate() {
        let numbers: Vec<u32> = line
            .unwrap()
            .split_whitespace()
            .map(|word| word.parse::<u32>().unwrap())
            .collect();
        mtx.add_row(index, &numbers);
    }
    mtx
}
