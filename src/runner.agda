{-# OPTIONS --with-K --guardedness #-}

module runner where

-- Imports

open import Function.Base using (_$_)
open import IO

open import runner-utils using (check-expected; day-runner)
import day01
import day02
-- import day03
-- import day04
-- import day05
-- import day06
-- import day07
-- import day08
-- import day09
-- import day10
-- import day11
-- import day12
-- import day13
-- import day14
-- import day15
-- import day16
-- import day17
-- import day18
-- import day19
-- import day19
-- import day20
-- import day21
-- import day22
-- import day23
-- import day24
-- import day25

-- Main

main : Main
main = run $ do
   day-runner day01.runner
   day-runner day02.runner
   -- day-runner day03.runner
   -- day-runner day04.runner
   -- day-runner day05.runner
  --  day-runner day06.runner
  --  day-runner day07.runner
  --  day-runner day08.runner
  --  day-runner day09.runner
  --  day-runner day10.runner
  --  day-runner day11.runner
  --  day-runner day12.runner
  --  day-runner day13.runner
  --  day-runner day14.runner
  --  day-runner day15.runner
  --  day-runner day16.runner
  --  day-runner day17.runner
  --  day-runner day18.runner
  --  day-runner day19.runner
  --  day-runner day20.runner
  --  day-runner day21.runner
  --  day-runner day22.runner
  --  day-runner day23.runner
  --  day-runner day24.runner
  --  day-runner day25.runner
