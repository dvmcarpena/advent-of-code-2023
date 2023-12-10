{-# OPTIONS --with-K --guardedness #-}

module runner where

-- Imports

open import Function.Base using (_$_)
open import IO

open import runner-utils using (check-expected; day-runner)
import Day01
import Day02
import Day03
-- import Day04
-- import Day05
-- import Day06
-- import Day07
-- import Day08
-- import Day09
-- import Day10
-- import Day11
-- import Day12
-- import Day13
-- import Day14
-- import Day15
-- import Day16
-- import Day17
-- import Day18
-- import Day19
-- import Day19
-- import Day20
-- import Day21
-- import Day22
-- import Day23
-- import Day24
-- import Day25

-- Main

main : Main
main = run $ do
   day-runner Day01.runner
   day-runner Day02.runner
   day-runner Day03.runner
   -- day-runner Day04.runner
   -- day-runner Day05.runner
  --  day-runner Day06.runner
  --  day-runner Day07.runner
  --  day-runner Day08.runner
  --  day-runner Day09.runner
  --  day-runner Day10.runner
  --  day-runner Day11.runner
  --  day-runner Day12.runner
  --  day-runner Day13.runner
  --  day-runner Day14.runner
  --  day-runner Day15.runner
  --  day-runner Day16.runner
  --  day-runner Day17.runner
  --  day-runner Day18.runner
  --  day-runner Day19.runner
  --  day-runner Day20.runner
  --  day-runner Day21.runner
  --  day-runner Day22.runner
  --  day-runner Day23.runner
  --  day-runner Day24.runner
  --  day-runner Day25.runner
