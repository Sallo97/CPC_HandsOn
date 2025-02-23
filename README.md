# [CPC] HandsOn and Quizzes
This repository contains my solution of all Hands-On exercises and additional puzzles for the 2024/2025 "Competitive Programming and Contests" course at the University of Pisa. All code is written in Rust.

## Table of Contents

- [HandsOn](#handson)
  - [HandsOn1 - Binary Tree](#handson1-binary-tree)
  - [HandsOn2 - Segment Tree](#handson2-segment-tree)
  - [HandsOn3 - Dynamic Programming](#handson3-dynamic-programming)


## HandsOn

### HandsOn1 - Binary Tree
Given a Rust's implementation of a Binary Tree, implement methods to solve the following exercises:

1. **Check if the tree is a Binary Search Tree:**
> Write a method to check if the binary tree is a Binary Search Tree. Recall that a Binary Search Tree is a binary tree where, for every node n in the tree, the maximum key in its left subtree is less than n’s key, and the minimum key in its right subtree is greater than n’s key.
2. **Find the Maximum Path Sum:**
> The task consists in finding the maximum sum of a simple path connecting two leaves in a given tree. The method should only return the sum of the found path.

### HandsOn2 - Segment Tree

1. **Min and Max**
> Given an array A[1,n] of n positive integers s.t each each x in A = O(n), build a data structure that answers in O(log(n)) time the following queries:
> * Update(i,j,T): ∀k in [1,n].A[k] = min(A[k], T)
> *  Max(i, j) : returns the largest value in A[i...j]

2. **Is There**
> Given a set of n segments S = {s1; ...; sn} s.t each si = (li, ri) where 0 <=li <= ri <= n-1, build a data structure to answer in O(log(n))
time the following query:
> * IsThere(i,j,k) = return 1 if ∃p in [i,j] s.t exactly k segments overlap position p, 0 otherwise.

### HandsOn3 - Dynamic Programming
1. **Holiday Planning**
> Given a number of days `D` and a set of cities to visit `C = {(a1,1, ..., a1,D); ..., (an,1, ..., an,D)}` where:
> > `a_i,j` represents the number of activities you can do in the `i`-th city on the `j`-th consecutive day you spend in that city.

> Find the the maximum number of activities possible in `D` days, visiting some of the available cities.

> Note :
> > Cities are visited sequentially from left to right.
> > You can choose to skip a city entirely.
> > Once you leave a city, you cannot return to it.

2. **Design a Course**
> Given a set of `n` topics, where each topic is represented by a tuple of two `u32` values:
> > The first element represents the topic's *beauty* (`bi`).
> > The second element represents the topic's *difficulty* (`di`).

> The task is to design a course as a sequence of topics such that: if a topic `t_i` with parameters `(b_i, d_i)` is included in the  course, then the next topic `t_j` (where `j > i`) must satisfy:

> > `b_j > b_i` (the beauty of the next topic is strictly greater than the current topic).

> >`d_j > d_i` (the difficulty of the next topic is strictly greater than the current topic).

> The goal is to find the maximum length of such a sequence of topics in `O(n log n)` time.

