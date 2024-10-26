-- \/\/\/ DO NOT MODIFY THIS FILE \/\/\/
module Sudoku(Board, Solutions(..)) where

{- The three possible numbers of solutions: 0, 1, or more than 1.
 -}
data Solutions = NoSolution | UniqueSolution | MultipleSolutions


{- A Sudoku board
   The board is represented as a list of rows,
   where each row is a list of ints,
   where 0 represents an empty cell.
   
   INVARIANTS:
   The length of the Board is the square of a positive integer.
   The board is square, so the length of a Board is the same as the length of each of its elements.
   The board contains only numbers between 0 and the length of the Board (inclusive).
 -}
type Board     = [[Int]]
