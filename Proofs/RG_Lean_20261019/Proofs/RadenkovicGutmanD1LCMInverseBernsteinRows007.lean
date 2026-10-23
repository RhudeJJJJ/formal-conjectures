/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow35 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 35 0 affine01753)
theorem bernsteinRow35_identity : bernsteinRow35=NestedInteger.coefficientFrom 88 35 0 affine01753 := by decide +kernel
theorem bernsteinRow35_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow35=true := by decide +kernel
#print axioms bernsteinRow35_identity
#print axioms bernsteinRow35_positive
def bernsteinRow36 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 36 0 affine01753)
theorem bernsteinRow36_identity : bernsteinRow36=NestedInteger.coefficientFrom 88 36 0 affine01753 := by decide +kernel
theorem bernsteinRow36_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow36=true := by decide +kernel
#print axioms bernsteinRow36_identity
#print axioms bernsteinRow36_positive
def bernsteinRow37 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 37 0 affine01753)
theorem bernsteinRow37_identity : bernsteinRow37=NestedInteger.coefficientFrom 88 37 0 affine01753 := by decide +kernel
theorem bernsteinRow37_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow37=true := by decide +kernel
#print axioms bernsteinRow37_identity
#print axioms bernsteinRow37_positive
def bernsteinRow38 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 38 0 affine01753)
theorem bernsteinRow38_identity : bernsteinRow38=NestedInteger.coefficientFrom 88 38 0 affine01753 := by decide +kernel
theorem bernsteinRow38_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow38=true := by decide +kernel
#print axioms bernsteinRow38_identity
#print axioms bernsteinRow38_positive
def bernsteinRow39 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 39 0 affine01753)
theorem bernsteinRow39_identity : bernsteinRow39=NestedInteger.coefficientFrom 88 39 0 affine01753 := by decide +kernel
theorem bernsteinRow39_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow39=true := by decide +kernel
#print axioms bernsteinRow39_identity
#print axioms bernsteinRow39_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
