/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow60 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 60 0 affine01753)
theorem bernsteinRow60_identity : bernsteinRow60=NestedInteger.coefficientFrom 88 60 0 affine01753 := by decide +kernel
theorem bernsteinRow60_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow60=true := by decide +kernel
#print axioms bernsteinRow60_identity
#print axioms bernsteinRow60_positive
def bernsteinRow61 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 61 0 affine01753)
theorem bernsteinRow61_identity : bernsteinRow61=NestedInteger.coefficientFrom 88 61 0 affine01753 := by decide +kernel
theorem bernsteinRow61_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow61=true := by decide +kernel
#print axioms bernsteinRow61_identity
#print axioms bernsteinRow61_positive
def bernsteinRow62 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 62 0 affine01753)
theorem bernsteinRow62_identity : bernsteinRow62=NestedInteger.coefficientFrom 88 62 0 affine01753 := by decide +kernel
theorem bernsteinRow62_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow62=true := by decide +kernel
#print axioms bernsteinRow62_identity
#print axioms bernsteinRow62_positive
def bernsteinRow63 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 63 0 affine01753)
theorem bernsteinRow63_identity : bernsteinRow63=NestedInteger.coefficientFrom 88 63 0 affine01753 := by decide +kernel
theorem bernsteinRow63_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow63=true := by decide +kernel
#print axioms bernsteinRow63_identity
#print axioms bernsteinRow63_positive
def bernsteinRow64 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 64 0 affine01753)
theorem bernsteinRow64_identity : bernsteinRow64=NestedInteger.coefficientFrom 88 64 0 affine01753 := by decide +kernel
theorem bernsteinRow64_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow64=true := by decide +kernel
#print axioms bernsteinRow64_identity
#print axioms bernsteinRow64_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
