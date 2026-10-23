/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights00 : List (Option ℤ) := [some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights00_identity : bernsteinWeights00=IntegerWeightedBernstein.weights 88 0 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights00_identity
def bernsteinRow00 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights00 affine01753)
theorem bernsteinRow00_weighted : bernsteinRow00=IntegerWeightedBernstein.applyWeights bernsteinWeights00 affine01753 := by decide +kernel
theorem bernsteinRow00_identity : bernsteinRow00=NestedInteger.coefficientFrom 88 0 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 0 0 affine01753 bernsteinRow00 bernsteinWeights00 bernsteinWeights00_identity bernsteinRow00_weighted
theorem bernsteinRow00_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow00=true := by decide +kernel
#print axioms bernsteinRow00_weighted
#print axioms bernsteinRow00_identity
#print axioms bernsteinRow00_positive
def bernsteinWeights01 : List (Option ℤ) := [some 88,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights01_identity : bernsteinWeights01=IntegerWeightedBernstein.weights 88 1 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights01_identity
def bernsteinRow01 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights01 affine01753)
theorem bernsteinRow01_weighted : bernsteinRow01=IntegerWeightedBernstein.applyWeights bernsteinWeights01 affine01753 := by decide +kernel
theorem bernsteinRow01_identity : bernsteinRow01=NestedInteger.coefficientFrom 88 1 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 1 0 affine01753 bernsteinRow01 bernsteinWeights01 bernsteinWeights01_identity bernsteinRow01_weighted
theorem bernsteinRow01_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow01=true := by decide +kernel
#print axioms bernsteinRow01_weighted
#print axioms bernsteinRow01_identity
#print axioms bernsteinRow01_positive
def bernsteinWeights02 : List (Option ℤ) := [some 3828,some 87,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights02_identity : bernsteinWeights02=IntegerWeightedBernstein.weights 88 2 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights02_identity
def bernsteinRow02 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights02 affine01753)
theorem bernsteinRow02_weighted : bernsteinRow02=IntegerWeightedBernstein.applyWeights bernsteinWeights02 affine01753 := by decide +kernel
theorem bernsteinRow02_identity : bernsteinRow02=NestedInteger.coefficientFrom 88 2 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 2 0 affine01753 bernsteinRow02 bernsteinWeights02 bernsteinWeights02_identity bernsteinRow02_weighted
theorem bernsteinRow02_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow02=true := by decide +kernel
#print axioms bernsteinRow02_weighted
#print axioms bernsteinRow02_identity
#print axioms bernsteinRow02_positive
def bernsteinWeights03 : List (Option ℤ) := [some 109736,some 3741,some 86,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights03_identity : bernsteinWeights03=IntegerWeightedBernstein.weights 88 3 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights03_identity
def bernsteinRow03 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights03 affine01753)
theorem bernsteinRow03_weighted : bernsteinRow03=IntegerWeightedBernstein.applyWeights bernsteinWeights03 affine01753 := by decide +kernel
theorem bernsteinRow03_identity : bernsteinRow03=NestedInteger.coefficientFrom 88 3 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 3 0 affine01753 bernsteinRow03 bernsteinWeights03 bernsteinWeights03_identity bernsteinRow03_weighted
theorem bernsteinRow03_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow03=true := by decide +kernel
#print axioms bernsteinRow03_weighted
#print axioms bernsteinRow03_identity
#print axioms bernsteinRow03_positive
def bernsteinWeights04 : List (Option ℤ) := [some 2331890,some 105995,some 3655,some 85,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights04_identity : bernsteinWeights04=IntegerWeightedBernstein.weights 88 4 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights04_identity
def bernsteinRow04 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights04 affine01753)
theorem bernsteinRow04_weighted : bernsteinRow04=IntegerWeightedBernstein.applyWeights bernsteinWeights04 affine01753 := by decide +kernel
theorem bernsteinRow04_identity : bernsteinRow04=NestedInteger.coefficientFrom 88 4 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 4 0 affine01753 bernsteinRow04 bernsteinWeights04 bernsteinWeights04_identity bernsteinRow04_weighted
theorem bernsteinRow04_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow04=true := by decide +kernel
#print axioms bernsteinRow04_weighted
#print axioms bernsteinRow04_identity
#print axioms bernsteinRow04_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
