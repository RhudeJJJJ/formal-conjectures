/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights05 : List (Option ℤ) := [some 39175752,some 2225895,some 102340,some 3570,some 84,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights05_identity : bernsteinWeights05=IntegerWeightedBernstein.weights 88 5 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights05_identity
def bernsteinRow05 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights05 affine01753)
theorem bernsteinRow05_weighted : bernsteinRow05=IntegerWeightedBernstein.applyWeights bernsteinWeights05 affine01753 := by decide +kernel
theorem bernsteinRow05_identity : bernsteinRow05=NestedInteger.coefficientFrom 88 5 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 5 0 affine01753 bernsteinRow05 bernsteinWeights05 bernsteinWeights05_identity bernsteinRow05_weighted
theorem bernsteinRow05_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow05=true := by decide +kernel
#print axioms bernsteinRow05_weighted
#print axioms bernsteinRow05_identity
#print axioms bernsteinRow05_positive
def bernsteinWeights06 : List (Option ℤ) := [some 541931236,some 36949857,some 2123555,some 98770,some 3486,some 83,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights06_identity : bernsteinWeights06=IntegerWeightedBernstein.weights 88 6 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights06_identity
def bernsteinRow06 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights06 affine01753)
theorem bernsteinRow06_weighted : bernsteinRow06=IntegerWeightedBernstein.applyWeights bernsteinWeights06 affine01753 := by decide +kernel
theorem bernsteinRow06_identity : bernsteinRow06=NestedInteger.coefficientFrom 88 6 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 6 0 affine01753 bernsteinRow06 bernsteinWeights06 bernsteinWeights06_identity bernsteinRow06_weighted
theorem bernsteinRow06_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow06=true := by decide +kernel
#print axioms bernsteinRow06_weighted
#print axioms bernsteinRow06_identity
#print axioms bernsteinRow06_positive
def bernsteinWeights07 : List (Option ℤ) := [some 6348337336,some 504981379,some 34826302,some 2024785,some 95284,some 3403,some 82,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights07_identity : bernsteinWeights07=IntegerWeightedBernstein.weights 88 7 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights07_identity
def bernsteinRow07 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights07 affine01753)
theorem bernsteinRow07_weighted : bernsteinRow07=IntegerWeightedBernstein.applyWeights bernsteinWeights07 affine01753 := by decide +kernel
theorem bernsteinRow07_identity : bernsteinRow07=NestedInteger.coefficientFrom 88 7 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 7 0 affine01753 bernsteinRow07 bernsteinWeights07 bernsteinWeights07_identity bernsteinRow07_weighted
theorem bernsteinRow07_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow07=true := by decide +kernel
#print axioms bernsteinRow07_weighted
#print axioms bernsteinRow07_identity
#print axioms bernsteinRow07_positive
def bernsteinWeights08 : List (Option ℤ) := [some 64276915527,some 5843355957,some 470155077,some 32801517,some 1929501,some 91881,some 3321,some 81,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights08_identity : bernsteinWeights08=IntegerWeightedBernstein.weights 88 8 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights08_identity
def bernsteinRow08 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights08 affine01753)
theorem bernsteinRow08_weighted : bernsteinRow08=IntegerWeightedBernstein.applyWeights bernsteinWeights08 affine01753 := by decide +kernel
theorem bernsteinRow08_identity : bernsteinRow08=NestedInteger.coefficientFrom 88 8 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 8 0 affine01753 bernsteinRow08 bernsteinWeights08 bernsteinWeights08_identity bernsteinRow08_weighted
theorem bernsteinRow08_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow08=true := by decide +kernel
#print axioms bernsteinRow08_weighted
#print axioms bernsteinRow08_identity
#print axioms bernsteinRow08_positive
def bernsteinWeights09 : List (Option ℤ) := [some 571350360240,some 58433559570,some 5373200880,some 437353560,some 30872016,some 1837620,some 88560,some 3240,some 80,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights09_identity : bernsteinWeights09=IntegerWeightedBernstein.weights 88 9 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights09_identity
def bernsteinRow09 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights09 affine01753)
theorem bernsteinRow09_weighted : bernsteinRow09=IntegerWeightedBernstein.applyWeights bernsteinWeights09 affine01753 := by decide +kernel
theorem bernsteinRow09_identity : bernsteinRow09=NestedInteger.coefficientFrom 88 9 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 9 0 affine01753 bernsteinRow09 bernsteinWeights09 bernsteinWeights09_identity bernsteinRow09_weighted
theorem bernsteinRow09_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow09=true := by decide +kernel
#print axioms bernsteinRow09_weighted
#print axioms bernsteinRow09_identity
#print axioms bernsteinRow09_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
