{-# OPTIONS --with-K --guardedness #-}

module runner where

-- Imports

open import Function.Base using (_$_)
open import IO

open import runner-utils using (check-expected; day-runner)
open import day01 renaming (enriched-runner to day01)
-- open import day02 renaming (enriched-runner to day02)
-- open import day03 renaming (enriched-runner to day03)
-- open import day04 renaming (enriched-runner to day04)
-- open import day05 renaming (enriched-runner to day05)
-- open import day06 renaming (enriched-runner to day06)
-- open import day07 renaming (enriched-runner to day07)
-- open import day08 renaming (enriched-runner to day08)
-- open import day09 renaming (enriched-runner to day09)
-- open import day10 renaming (enriched-runner to day10)
-- open import day11 renaming (enriched-runner to day11)
-- open import day12 renaming (enriched-runner to day12)
-- open import day13 renaming (enriched-runner to day13)
-- open import day14 renaming (enriched-runner to day14)
-- open import day15 renaming (enriched-runner to day15)
-- open import day16 renaming (enriched-runner to day16)
-- open import day17 renaming (enriched-runner to day17)
-- open import day18 renaming (enriched-runner to day18)
-- open import day19 renaming (enriched-runner to day19)
-- open import day20 renaming (enriched-runner to day20)
-- open import day21 renaming (enriched-runner to day21)
-- open import day22 renaming (enriched-runner to day22)
-- open import day23 renaming (enriched-runner to day23)
-- open import day24 renaming (enriched-runner to day24)
-- open import day25 renaming (enriched-runner to day25)

-- Main

main : Main
main = run $ do
   day-runner day01
   -- day-runner day02
   -- day-runner day03
   -- day-runner day04
   -- day-runner day05
  --  day-runner day06
  --  day-runner day07
  --  day-runner day08
  --  day-runner day09
  --  day-runner day10
  --  day-runner day11
  --  day-runner day12
  --  day-runner day13
  --  day-runner day14
  --  day-runner day15
  --  day-runner day16
  --  day-runner day17
  --  day-runner day18
  --  day-runner day19
  --  day-runner day20
  --  day-runner day21
  --  day-runner day22
  --  day-runner day23
  --  day-runner day24
  --  day-runner day25
