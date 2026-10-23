/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights15 : List (Option ℤ) := [some 31731084956648880,some 5408707663065150,some 870366750378300,some 131567066917650,some 18574174153080,some 2432332329570,some 293052087900,some 32164253550,some 3176716400,some 277962685,some 21111090,some 1353275,some 70300,some 2775,some 74,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights15_identity : bernsteinWeights15=IntegerWeightedBernstein.weights 88 15 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights15_identity
def bernsteinRow15 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights15 affine01753)
theorem bernsteinRow15_weighted : bernsteinRow15=IntegerWeightedBernstein.applyWeights bernsteinWeights15 affine01753 := by decide +kernel
theorem bernsteinRow15_identity : bernsteinRow15=NestedInteger.coefficientFrom 88 15 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 15 0 affine01753 bernsteinRow15 bernsteinWeights15 bernsteinWeights15_identity bernsteinRow15_weighted
theorem bernsteinRow15_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow15=true := by decide +kernel
#print axioms bernsteinRow15_weighted
#print axioms bernsteinRow15_identity
#print axioms bernsteinRow15_positive
def bernsteinWeights16 : List (Option ℤ) := [some 144773075114710515,some 26322377293583730,some 4538340912686850,some 738799683460650,some 112992892764570,some 16141841823510,some 2139280241670,some 260887834350,some 28987537150,some 2898753715,some 256851595,some 19757815,some 1282975,some 67525,some 2701,some 73,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights16_identity : bernsteinWeights16=IntegerWeightedBernstein.weights 88 16 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights16_identity
def bernsteinRow16 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights16 affine01753)
theorem bernsteinRow16_weighted : bernsteinRow16=IntegerWeightedBernstein.applyWeights bernsteinWeights16 affine01753 := by decide +kernel
theorem bernsteinRow16_identity : bernsteinRow16=NestedInteger.coefficientFrom 88 16 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 16 0 affine01753 bernsteinRow16 bernsteinWeights16 bernsteinWeights16_identity bernsteinRow16_weighted
theorem bernsteinRow16_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow16=true := by decide +kernel
#print axioms bernsteinRow16_weighted
#print axioms bernsteinRow16_identity
#print axioms bernsteinRow16_positive
def bernsteinWeights17 : List (Option ℤ) := [some 613156553427009240,some 118450697821126785,some 21784036380896880,some 3799541229226200,some 625806790696080,some 96851050941060,some 14002561581840,some 1878392407320,some 231900297200,some 26088783435,some 2641902120,some 237093780,some 18474840,some 1215450,some 64824,some 2628,some 72,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights17_identity : bernsteinWeights17=IntegerWeightedBernstein.weights 88 17 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights17_identity
def bernsteinRow17 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights17 affine01753)
theorem bernsteinRow17_weighted : bernsteinRow17=IntegerWeightedBernstein.applyWeights bernsteinWeights17 affine01753 := by decide +kernel
theorem bernsteinRow17_identity : bernsteinRow17=NestedInteger.coefficientFrom 88 17 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 17 0 affine01753 bernsteinRow17 bernsteinWeights17 bernsteinWeights17_identity bernsteinRow17_weighted
theorem bernsteinRow17_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow17=true := by decide +kernel
#print axioms bernsteinRow17_weighted
#print axioms bernsteinRow17_identity
#print axioms bernsteinRow17_positive
def bernsteinWeights18 : List (Option ℤ) := [some 2418561960739869780,some 494705855605882455,some 96666661440229905,some 17984495151670680,some 3173734438530120,some 528955739755020,some 82848489359220,some 12124169174520,some 1646492110120,some 205811513765,some 23446881315,some 2404808340,some 218618940,some 17259390,some 1150626,some 62196,some 2556,some 71,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights18_identity : bernsteinWeights18=IntegerWeightedBernstein.weights 88 18 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights18_identity
def bernsteinRow18 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights18 affine01753)
theorem bernsteinRow18_weighted : bernsteinRow18=IntegerWeightedBernstein.applyWeights bernsteinWeights18 affine01753 := by decide +kernel
theorem bernsteinRow18_identity : bernsteinRow18=NestedInteger.coefficientFrom 88 18 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 18 0 affine01753 bernsteinRow18 bernsteinWeights18 bernsteinWeights18_identity bernsteinRow18_weighted
theorem bernsteinRow18_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow18=true := by decide +kernel
#print axioms bernsteinRow18_weighted
#print axioms bernsteinRow18_identity
#print axioms bernsteinRow18_positive
def bernsteinWeights19 : List (Option ℤ) := [some 8910491434304783400,some 1923856105133987325,some 398039194165652550,some 78682166288559225,some 14810760713140560,some 2644778698775100,some 446107250395800,some 70724320184700,some 10477677064400,some 1440680596355,some 182364632450,some 21042072975,some 2186189400,some 201359550,some 16108764,some 1088430,some 59640,some 2485,some 70,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights19_identity : bernsteinWeights19=IntegerWeightedBernstein.weights 88 19 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights19_identity
def bernsteinRow19 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights19 affine01753)
theorem bernsteinRow19_weighted : bernsteinRow19=IntegerWeightedBernstein.applyWeights bernsteinWeights19 affine01753 := by decide +kernel
theorem bernsteinRow19_identity : bernsteinRow19=NestedInteger.coefficientFrom 88 19 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 19 0 affine01753 bernsteinRow19 bernsteinWeights19 bernsteinWeights19_identity bernsteinRow19_weighted
theorem bernsteinRow19_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow19=true := by decide +kernel
#print axioms bernsteinRow19_weighted
#print axioms bernsteinRow19_identity
#print axioms bernsteinRow19_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
