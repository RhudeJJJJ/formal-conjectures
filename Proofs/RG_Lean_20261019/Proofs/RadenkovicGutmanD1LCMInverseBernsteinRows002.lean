/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow10 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 10 0 affine01753)
theorem bernsteinRow10_identity : bernsteinRow10=NestedInteger.coefficientFrom 88 10 0 affine01753 := by decide +kernel
theorem bernsteinRow10_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow10=true := by decide +kernel
#print axioms bernsteinRow10_identity
#print axioms bernsteinRow10_positive
def bernsteinRow11 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 11 0 affine01753)
theorem bernsteinRow11_identity : bernsteinRow11=NestedInteger.coefficientFrom 88 11 0 affine01753 := by decide +kernel
theorem bernsteinRow11_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow11=true := by decide +kernel
#print axioms bernsteinRow11_identity
#print axioms bernsteinRow11_positive
def bernsteinRow12 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 12 0 affine01753)
theorem bernsteinRow12_identity : bernsteinRow12=NestedInteger.coefficientFrom 88 12 0 affine01753 := by decide +kernel
theorem bernsteinRow12_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow12=true := by decide +kernel
#print axioms bernsteinRow12_identity
#print axioms bernsteinRow12_positive
def bernsteinRow13 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 13 0 affine01753)
theorem bernsteinRow13_identity : bernsteinRow13=NestedInteger.coefficientFrom 88 13 0 affine01753 := by decide +kernel
theorem bernsteinRow13_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow13=true := by decide +kernel
#print axioms bernsteinRow13_identity
#print axioms bernsteinRow13_positive
def bernsteinRow14 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 14 0 affine01753)
theorem bernsteinRow14_identity : bernsteinRow14=NestedInteger.coefficientFrom 88 14 0 affine01753 := by decide +kernel
theorem bernsteinRow14_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow14=true := by decide +kernel
#print axioms bernsteinRow14_identity
#print axioms bernsteinRow14_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
