# [CPC] HandsOn and Quizzes
This repository contains the implementations of all Hands-On exercises and additional puzzles for the 2024/2025 "Competitive Programming and Contests" course at the University of Pisa. All code is written in Rust.

## Table of Contents

- [HandsOn](#handson)
  - [HandsOn1 - Binary Tree](#handson1-binary-tree)
  - [HandsOn2 - Segment Tree](#handson2-segment-tree)


## HandsOn

### HandsOn1 - Binary Tree
Given a Rust's implementation of a Binary Tree, implement methods to solve the following exercises:

1. **Check if the tree is a Binary Search Tree:**
Write a method to check if the binary tree is a Binary Search Tree. Recall that a Binary Search Tree is a binary tree where, for every node n in the tree, the maximum key in its left subtree is less than n’s key, and the minimum key in its right subtree is greater than n’s key.
2. **Find the Maximum Path Sum:**
The task consists in finding the maximum sum of a simple path connecting two leaves in a given tree. The method should only return the sum of the found path.

### HandsOn2 - Segment Tree
Solve the following problems using suitable data structures

1. **Min and Max**
> Given an array A[1,n] of n positive integers s.t each each x in A = O(n), build a data structure that answers in O(log(n)) time the following queries:
> * Update(i,j,T): ∀k in [1,n].A[k] = min(A[k], T)
> *  Max(i, j) : returns the largest value in A[i...j]

2. **Is There**
> Given a set of n segments S = {s1; ...; sn} s.t each si = (li, ri) where 0 <=li <= ri <= n-1, build a data structure to answer in O(log(n))
time the following query:
> * IsThere(i,j,k) = return 1 if ∃p in [i,j] s.t exactly k segments overlap position p, 0 otherwise.
