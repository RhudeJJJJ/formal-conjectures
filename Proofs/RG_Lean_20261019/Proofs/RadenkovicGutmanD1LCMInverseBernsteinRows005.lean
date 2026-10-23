/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow25 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 25 0 affine01753)
theorem bernsteinRow25_identity : bernsteinRow25=NestedInteger.coefficientFrom 88 25 0 affine01753 := by decide +kernel
theorem bernsteinRow25_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow25=true := by decide +kernel
#print axioms bernsteinRow25_identity
#print axioms bernsteinRow25_positive
def bernsteinRow26 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 26 0 affine01753)
theorem bernsteinRow26_identity : bernsteinRow26=NestedInteger.coefficientFrom 88 26 0 affine01753 := by decide +kernel
theorem bernsteinRow26_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow26=true := by decide +kernel
#print axioms bernsteinRow26_identity
#print axioms bernsteinRow26_positive
def bernsteinRow27 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 27 0 affine01753)
theorem bernsteinRow27_identity : bernsteinRow27=NestedInteger.coefficientFrom 88 27 0 affine01753 := by decide +kernel
theorem bernsteinRow27_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow27=true := by decide +kernel
#print axioms bernsteinRow27_identity
#print axioms bernsteinRow27_positive
def bernsteinRow28 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 28 0 affine01753)
theorem bernsteinRow28_identity : bernsteinRow28=NestedInteger.coefficientFrom 88 28 0 affine01753 := by decide +kernel
theorem bernsteinRow28_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow28=true := by decide +kernel
#print axioms bernsteinRow28_identity
#print axioms bernsteinRow28_positive
def bernsteinRow29 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 29 0 affine01753)
theorem bernsteinRow29_identity : bernsteinRow29=NestedInteger.coefficientFrom 88 29 0 affine01753 := by decide +kernel
theorem bernsteinRow29_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow29=true := by decide +kernel
#print axioms bernsteinRow29_identity
#print axioms bernsteinRow29_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
