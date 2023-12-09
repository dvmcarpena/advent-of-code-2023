{-# OPTIONS --cubical-compatible --guardedness #-}

module runner-utils where

-- Imports

open import Function.Base using (_$_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_; _==_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import IO

open import utils using (Runner)

-- Utils

check-expected : String → String → IO (String × String)
check-expected day result = do
  expected ← readFiniteFile ("./input/" ++ day ++ "-result.txt")
  return $ 
    if result == expected 
    then ("✅" , result) 
    else ("❌" , "Expected:\n\n" ++ expected ++ "\n\nFound:\n\n" ++ result)

day-runner : Runner → IO _ 
day-runner (runner , day , title) = do
  content ← readFiniteFile ("./input/" ++ day ++ "-input.txt")
  let result = runner content
  (expected , result) ← if true then (check-expected day result) else return ("?" , result)
  putStrLn $ title 
    ++ " " 
    ++ expected 
    ++ " -----------------------------------------\n\n" 
    ++ result 
    ++ "\n"
