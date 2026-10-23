/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights85 : List (Option ℤ) := [some 109736,some 105995,some 102340,some 98770,some 95284,some 91881,some 88560,some 85320,some 82160,some 79079,some 76076,some 73150,some 70300,some 67525,some 64824,some 62196,some 59640,some 57155,some 54740,some 52394,some 50116,some 47905,some 45760,some 43680,some 41664,some 39711,some 37820,some 35990,some 34220,some 32509,some 30856,some 29260,some 27720,some 26235,some 24804,some 23426,some 22100,some 20825,some 19600,some 18424,some 17296,some 16215,some 15180,some 14190,some 13244,some 12341,some 11480,some 10660,some 9880,some 9139,some 8436,some 7770,some 7140,some 6545,some 5984,some 5456,some 4960,some 4495,some 4060,some 3654,some 3276,some 2925,some 2600,some 2300,some 2024,some 1771,some 1540,some 1330,some 1140,some 969,some 816,some 680,some 560,some 455,some 364,some 286,some 220,some 165,some 120,some 84,some 56,some 35,some 20,some 10,some 4,some 1,none,none,none]
theorem bernsteinWeights85_identity : bernsteinWeights85=IntegerWeightedBernstein.weights 88 85 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights85_identity
def bernsteinRow85 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights85 affine01753)
theorem bernsteinRow85_weighted : bernsteinRow85=IntegerWeightedBernstein.applyWeights bernsteinWeights85 affine01753 := by decide +kernel
theorem bernsteinRow85_identity : bernsteinRow85=NestedInteger.coefficientFrom 88 85 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 85 0 affine01753 bernsteinRow85 bernsteinWeights85 bernsteinWeights85_identity bernsteinRow85_weighted
theorem bernsteinRow85_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow85=true := by decide +kernel
#print axioms bernsteinRow85_weighted
#print axioms bernsteinRow85_identity
#print axioms bernsteinRow85_positive
def bernsteinWeights86 : List (Option ℤ) := [some 3828,some 3741,some 3655,some 3570,some 3486,some 3403,some 3321,some 3240,some 3160,some 3081,some 3003,some 2926,some 2850,some 2775,some 2701,some 2628,some 2556,some 2485,some 2415,some 2346,some 2278,some 2211,some 2145,some 2080,some 2016,some 1953,some 1891,some 1830,some 1770,some 1711,some 1653,some 1596,some 1540,some 1485,some 1431,some 1378,some 1326,some 1275,some 1225,some 1176,some 1128,some 1081,some 1035,some 990,some 946,some 903,some 861,some 820,some 780,some 741,some 703,some 666,some 630,some 595,some 561,some 528,some 496,some 465,some 435,some 406,some 378,some 351,some 325,some 300,some 276,some 253,some 231,some 210,some 190,some 171,some 153,some 136,some 120,some 105,some 91,some 78,some 66,some 55,some 45,some 36,some 28,some 21,some 15,some 10,some 6,some 3,some 1,none,none]
theorem bernsteinWeights86_identity : bernsteinWeights86=IntegerWeightedBernstein.weights 88 86 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights86_identity
def bernsteinRow86 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights86 affine01753)
theorem bernsteinRow86_weighted : bernsteinRow86=IntegerWeightedBernstein.applyWeights bernsteinWeights86 affine01753 := by decide +kernel
theorem bernsteinRow86_identity : bernsteinRow86=NestedInteger.coefficientFrom 88 86 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 86 0 affine01753 bernsteinRow86 bernsteinWeights86 bernsteinWeights86_identity bernsteinRow86_weighted
theorem bernsteinRow86_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow86=true := by decide +kernel
#print axioms bernsteinRow86_weighted
#print axioms bernsteinRow86_identity
#print axioms bernsteinRow86_positive
def bernsteinWeights87 : List (Option ℤ) := [some 88,some 87,some 86,some 85,some 84,some 83,some 82,some 81,some 80,some 79,some 78,some 77,some 76,some 75,some 74,some 73,some 72,some 71,some 70,some 69,some 68,some 67,some 66,some 65,some 64,some 63,some 62,some 61,some 60,some 59,some 58,some 57,some 56,some 55,some 54,some 53,some 52,some 51,some 50,some 49,some 48,some 47,some 46,some 45,some 44,some 43,some 42,some 41,some 40,some 39,some 38,some 37,some 36,some 35,some 34,some 33,some 32,some 31,some 30,some 29,some 28,some 27,some 26,some 25,some 24,some 23,some 22,some 21,some 20,some 19,some 18,some 17,some 16,some 15,some 14,some 13,some 12,some 11,some 10,some 9,some 8,some 7,some 6,some 5,some 4,some 3,some 2,some 1,none]
theorem bernsteinWeights87_identity : bernsteinWeights87=IntegerWeightedBernstein.weights 88 87 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights87_identity
def bernsteinRow87 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights87 affine01753)
theorem bernsteinRow87_weighted : bernsteinRow87=IntegerWeightedBernstein.applyWeights bernsteinWeights87 affine01753 := by decide +kernel
theorem bernsteinRow87_identity : bernsteinRow87=NestedInteger.coefficientFrom 88 87 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 87 0 affine01753 bernsteinRow87 bernsteinWeights87 bernsteinWeights87_identity bernsteinRow87_weighted
theorem bernsteinRow87_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow87=true := by decide +kernel
#print axioms bernsteinRow87_weighted
#print axioms bernsteinRow87_identity
#print axioms bernsteinRow87_positive
def bernsteinWeights88 : List (Option ℤ) := [some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1,some 1]
theorem bernsteinWeights88_identity : bernsteinWeights88=IntegerWeightedBernstein.weights 88 88 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights88_identity
def bernsteinRow88 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights88 affine01753)
theorem bernsteinRow88_weighted : bernsteinRow88=IntegerWeightedBernstein.applyWeights bernsteinWeights88 affine01753 := by decide +kernel
theorem bernsteinRow88_identity : bernsteinRow88=NestedInteger.coefficientFrom 88 88 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 88 0 affine01753 bernsteinRow88 bernsteinWeights88 bernsteinWeights88_identity bernsteinRow88_weighted
theorem bernsteinRow88_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow88=true := by decide +kernel
#print axioms bernsteinRow88_weighted
#print axioms bernsteinRow88_identity
#print axioms bernsteinRow88_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
