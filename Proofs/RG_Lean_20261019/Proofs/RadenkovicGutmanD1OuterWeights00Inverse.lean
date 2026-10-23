/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerOuterTable
import Proofs.RadenkovicGutmanIntegerBernsteinRows
namespace Gebendorfer.RadenkovicGutman.DegreeOneOuterWeights00Inverse
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def part00 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 0 (List.replicate 12 (0 : ℤ)))
theorem part00_identity : part00=IntegerWeightedOuter.weights (n := 0) 1 1 1024 0 (List.replicate 12 (0 : ℤ)) := by decide +kernel
#print axioms part00_identity
def part01 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 12 (List.replicate 12 (0 : ℤ)))
theorem part01_identity : part01=IntegerWeightedOuter.weights (n := 0) 1 1 1024 12 (List.replicate 12 (0 : ℤ)) := by decide +kernel
#print axioms part01_identity
def part02 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 24 (List.replicate 12 (0 : ℤ)))
theorem part02_identity : part02=IntegerWeightedOuter.weights (n := 0) 1 1 1024 24 (List.replicate 12 (0 : ℤ)) := by decide +kernel
#print axioms part02_identity
def part03 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 36 (List.replicate 12 (0 : ℤ)))
theorem part03_identity : part03=IntegerWeightedOuter.weights (n := 0) 1 1 1024 36 (List.replicate 12 (0 : ℤ)) := by decide +kernel
#print axioms part03_identity
def part04 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 48 (List.replicate 12 (0 : ℤ)))
theorem part04_identity : part04=IntegerWeightedOuter.weights (n := 0) 1 1 1024 48 (List.replicate 12 (0 : ℤ)) := by decide +kernel
#print axioms part04_identity
def part05 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 60 (List.replicate 12 (0 : ℤ)))
theorem part05_identity : part05=IntegerWeightedOuter.weights (n := 0) 1 1 1024 60 (List.replicate 12 (0 : ℤ)) := by decide +kernel
#print axioms part05_identity
def part06 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 72 (List.replicate 12 (0 : ℤ)))
theorem part06_identity : part06=IntegerWeightedOuter.weights (n := 0) 1 1 1024 72 (List.replicate 12 (0 : ℤ)) := by decide +kernel
#print axioms part06_identity
def part07 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights (n := 0) 1 1 1024 84 (List.replicate 5 (0 : ℤ)))
theorem part07_identity : part07=IntegerWeightedOuter.weights (n := 0) 1 1 1024 84 (List.replicate 5 (0 : ℤ)) := by decide +kernel
#print axioms part07_identity
end Gebendorfer.RadenkovicGutman.DegreeOneOuterWeights00Inverse
