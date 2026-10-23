/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow50 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 50 0 affine01753)
theorem bernsteinRow50_identity : bernsteinRow50=NestedInteger.coefficientFrom 88 50 0 affine01753 := by decide +kernel
theorem bernsteinRow50_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow50=true := by decide +kernel
#print axioms bernsteinRow50_identity
#print axioms bernsteinRow50_positive
def bernsteinRow51 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 51 0 affine01753)
theorem bernsteinRow51_identity : bernsteinRow51=NestedInteger.coefficientFrom 88 51 0 affine01753 := by decide +kernel
theorem bernsteinRow51_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow51=true := by decide +kernel
#print axioms bernsteinRow51_identity
#print axioms bernsteinRow51_positive
def bernsteinRow52 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 52 0 affine01753)
theorem bernsteinRow52_identity : bernsteinRow52=NestedInteger.coefficientFrom 88 52 0 affine01753 := by decide +kernel
theorem bernsteinRow52_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow52=true := by decide +kernel
#print axioms bernsteinRow52_identity
#print axioms bernsteinRow52_positive
def bernsteinRow53 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 53 0 affine01753)
theorem bernsteinRow53_identity : bernsteinRow53=NestedInteger.coefficientFrom 88 53 0 affine01753 := by decide +kernel
theorem bernsteinRow53_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow53=true := by decide +kernel
#print axioms bernsteinRow53_identity
#print axioms bernsteinRow53_positive
def bernsteinRow54 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 54 0 affine01753)
theorem bernsteinRow54_identity : bernsteinRow54=NestedInteger.coefficientFrom 88 54 0 affine01753 := by decide +kernel
theorem bernsteinRow54_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow54=true := by decide +kernel
#print axioms bernsteinRow54_identity
#print axioms bernsteinRow54_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
