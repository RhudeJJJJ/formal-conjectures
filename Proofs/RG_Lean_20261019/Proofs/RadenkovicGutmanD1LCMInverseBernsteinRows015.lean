/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow75 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 75 0 affine01753)
theorem bernsteinRow75_identity : bernsteinRow75=NestedInteger.coefficientFrom 88 75 0 affine01753 := by decide +kernel
theorem bernsteinRow75_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow75=true := by decide +kernel
#print axioms bernsteinRow75_identity
#print axioms bernsteinRow75_positive
def bernsteinRow76 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 76 0 affine01753)
theorem bernsteinRow76_identity : bernsteinRow76=NestedInteger.coefficientFrom 88 76 0 affine01753 := by decide +kernel
theorem bernsteinRow76_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow76=true := by decide +kernel
#print axioms bernsteinRow76_identity
#print axioms bernsteinRow76_positive
def bernsteinRow77 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 77 0 affine01753)
theorem bernsteinRow77_identity : bernsteinRow77=NestedInteger.coefficientFrom 88 77 0 affine01753 := by decide +kernel
theorem bernsteinRow77_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow77=true := by decide +kernel
#print axioms bernsteinRow77_identity
#print axioms bernsteinRow77_positive
def bernsteinRow78 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 78 0 affine01753)
theorem bernsteinRow78_identity : bernsteinRow78=NestedInteger.coefficientFrom 88 78 0 affine01753 := by decide +kernel
theorem bernsteinRow78_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow78=true := by decide +kernel
#print axioms bernsteinRow78_identity
#print axioms bernsteinRow78_positive
def bernsteinRow79 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 79 0 affine01753)
theorem bernsteinRow79_identity : bernsteinRow79=NestedInteger.coefficientFrom 88 79 0 affine01753 := by decide +kernel
theorem bernsteinRow79_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow79=true := by decide +kernel
#print axioms bernsteinRow79_identity
#print axioms bernsteinRow79_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
