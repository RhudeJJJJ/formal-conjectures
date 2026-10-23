/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights10 : List (Option ℤ) := [some 4513667845896,some 512916800670,some 53060358690,some 4935847320,some 406481544,some 29034396,some 1749060,some 85320,some 3160,some 79,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights10_identity : bernsteinWeights10=IntegerWeightedBernstein.weights 88 10 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights10_identity
def bernsteinRow10 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights10 affine01753)
theorem bernsteinRow10_weighted : bernsteinRow10=IntegerWeightedBernstein.applyWeights bernsteinWeights10 affine01753 := by decide +kernel
theorem bernsteinRow10_identity : bernsteinRow10=NestedInteger.coefficientFrom 88 10 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 10 0 affine01753 bernsteinRow10 bernsteinWeights10 bernsteinWeights10_identity bernsteinRow10_weighted
theorem bernsteinRow10_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow10=true := by decide +kernel
#print axioms bernsteinRow10_weighted
#print axioms bernsteinRow10_identity
#print axioms bernsteinRow10_positive
def bernsteinWeights11 : List (Option ℤ) := [some 32006008361808,some 4000751045226,some 459856441980,some 48124511370,some 4529365776,some 377447148,some 27285336,some 1663740,some 82160,some 3081,some 78,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights11_identity : bernsteinWeights11=IntegerWeightedBernstein.weights 88 11 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights11_identity
def bernsteinRow11 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights11 affine01753)
theorem bernsteinRow11_weighted : bernsteinRow11=IntegerWeightedBernstein.applyWeights bernsteinWeights11 affine01753 := by decide +kernel
theorem bernsteinRow11_identity : bernsteinRow11=NestedInteger.coefficientFrom 88 11 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 11 0 affine01753 bernsteinRow11 bernsteinWeights11 bernsteinWeights11_identity bernsteinRow11_weighted
theorem bernsteinRow11_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow11=true := by decide +kernel
#print axioms bernsteinRow11_weighted
#print axioms bernsteinRow11_identity
#print axioms bernsteinRow11_positive
def bernsteinWeights12 : List (Option ℤ) := [some 205371886988268,some 28005257316582,some 3540894603246,some 411731930610,some 43595145594,some 4151918628,some 350161812,some 25621596,some 1581580,some 79079,some 3003,some 77,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights12_identity : bernsteinWeights12=IntegerWeightedBernstein.weights 88 12 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights12_identity
def bernsteinRow12 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights12 affine01753)
theorem bernsteinRow12_weighted : bernsteinRow12=IntegerWeightedBernstein.applyWeights bernsteinWeights12 affine01753 := by decide +kernel
theorem bernsteinRow12_identity : bernsteinRow12=NestedInteger.coefficientFrom 88 12 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 12 0 affine01753 bernsteinRow12 bernsteinWeights12 bernsteinWeights12_identity bernsteinRow12_weighted
theorem bernsteinRow12_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow12=true := by decide +kernel
#print axioms bernsteinRow12_weighted
#print axioms bernsteinRow12_identity
#print axioms bernsteinRow12_positive
def bernsteinWeights13 : List (Option ℤ) := [some 1200635647008336,some 177366629671686,some 24464362713336,some 3129162672636,some 368136785016,some 39443226966,some 3801756816,some 324540216,some 24040016,some 1502501,some 76076,some 2926,some 76,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights13_identity : bernsteinWeights13=IntegerWeightedBernstein.weights 88 13 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights13_identity
def bernsteinRow13 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights13 affine01753)
theorem bernsteinRow13_weighted : bernsteinRow13=IntegerWeightedBernstein.applyWeights bernsteinWeights13 affine01753 := by decide +kernel
theorem bernsteinRow13_identity : bernsteinRow13=NestedInteger.coefficientFrom 88 13 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 13 0 affine01753 bernsteinRow13 bernsteinWeights13 bernsteinWeights13_identity bernsteinRow13_weighted
theorem bernsteinRow13_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow13=true := by decide +kernel
#print axioms bernsteinRow13_weighted
#print axioms bernsteinRow13_identity
#print axioms bernsteinRow13_positive
def bernsteinWeights14 : List (Option ℤ) := [some 6431976680401800,some 1023269017336650,some 152902266958350,some 21335200040700,some 2761025887620,some 328693558050,some 35641470150,some 3477216600,some 300500200,some 22537515,some 1426425,some 73150,some 2850,some 75,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights14_identity : bernsteinWeights14=IntegerWeightedBernstein.weights 88 14 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights14_identity
def bernsteinRow14 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights14 affine01753)
theorem bernsteinRow14_weighted : bernsteinRow14=IntegerWeightedBernstein.applyWeights bernsteinWeights14 affine01753 := by decide +kernel
theorem bernsteinRow14_identity : bernsteinRow14=NestedInteger.coefficientFrom 88 14 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 14 0 affine01753 bernsteinRow14 bernsteinWeights14 bernsteinWeights14_identity bernsteinRow14_weighted
theorem bernsteinRow14_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow14=true := by decide +kernel
#print axioms bernsteinRow14_weighted
#print axioms bernsteinRow14_identity
#print axioms bernsteinRow14_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
