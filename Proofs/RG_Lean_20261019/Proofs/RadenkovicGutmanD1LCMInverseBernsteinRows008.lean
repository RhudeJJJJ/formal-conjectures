/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow40 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 40 0 affine01753)
theorem bernsteinRow40_identity : bernsteinRow40=NestedInteger.coefficientFrom 88 40 0 affine01753 := by decide +kernel
theorem bernsteinRow40_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow40=true := by decide +kernel
#print axioms bernsteinRow40_identity
#print axioms bernsteinRow40_positive
def bernsteinRow41 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 41 0 affine01753)
theorem bernsteinRow41_identity : bernsteinRow41=NestedInteger.coefficientFrom 88 41 0 affine01753 := by decide +kernel
theorem bernsteinRow41_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow41=true := by decide +kernel
#print axioms bernsteinRow41_identity
#print axioms bernsteinRow41_positive
def bernsteinRow42 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 42 0 affine01753)
theorem bernsteinRow42_identity : bernsteinRow42=NestedInteger.coefficientFrom 88 42 0 affine01753 := by decide +kernel
theorem bernsteinRow42_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow42=true := by decide +kernel
#print axioms bernsteinRow42_identity
#print axioms bernsteinRow42_positive
def bernsteinRow43 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 43 0 affine01753)
theorem bernsteinRow43_identity : bernsteinRow43=NestedInteger.coefficientFrom 88 43 0 affine01753 := by decide +kernel
theorem bernsteinRow43_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow43=true := by decide +kernel
#print axioms bernsteinRow43_identity
#print axioms bernsteinRow43_positive
def bernsteinRow44 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 44 0 affine01753)
theorem bernsteinRow44_identity : bernsteinRow44=NestedInteger.coefficientFrom 88 44 0 affine01753 := by decide +kernel
theorem bernsteinRow44_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow44=true := by decide +kernel
#print axioms bernsteinRow44_identity
#print axioms bernsteinRow44_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
