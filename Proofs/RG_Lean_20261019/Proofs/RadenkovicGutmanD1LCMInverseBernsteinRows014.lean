/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow70 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 70 0 affine01753)
theorem bernsteinRow70_identity : bernsteinRow70=NestedInteger.coefficientFrom 88 70 0 affine01753 := by decide +kernel
theorem bernsteinRow70_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow70=true := by decide +kernel
#print axioms bernsteinRow70_identity
#print axioms bernsteinRow70_positive
def bernsteinRow71 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 71 0 affine01753)
theorem bernsteinRow71_identity : bernsteinRow71=NestedInteger.coefficientFrom 88 71 0 affine01753 := by decide +kernel
theorem bernsteinRow71_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow71=true := by decide +kernel
#print axioms bernsteinRow71_identity
#print axioms bernsteinRow71_positive
def bernsteinRow72 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 72 0 affine01753)
theorem bernsteinRow72_identity : bernsteinRow72=NestedInteger.coefficientFrom 88 72 0 affine01753 := by decide +kernel
theorem bernsteinRow72_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow72=true := by decide +kernel
#print axioms bernsteinRow72_identity
#print axioms bernsteinRow72_positive
def bernsteinRow73 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 73 0 affine01753)
theorem bernsteinRow73_identity : bernsteinRow73=NestedInteger.coefficientFrom 88 73 0 affine01753 := by decide +kernel
theorem bernsteinRow73_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow73=true := by decide +kernel
#print axioms bernsteinRow73_identity
#print axioms bernsteinRow73_positive
def bernsteinRow74 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 74 0 affine01753)
theorem bernsteinRow74_identity : bernsteinRow74=NestedInteger.coefficientFrom 88 74 0 affine01753 := by decide +kernel
theorem bernsteinRow74_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow74=true := by decide +kernel
#print axioms bernsteinRow74_identity
#print axioms bernsteinRow74_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
