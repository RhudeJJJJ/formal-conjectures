/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow00 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 0 0 affine01753)
theorem bernsteinRow00_identity : bernsteinRow00=NestedInteger.coefficientFrom 88 0 0 affine01753 := by decide +kernel
theorem bernsteinRow00_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow00=true := by decide +kernel
#print axioms bernsteinRow00_identity
#print axioms bernsteinRow00_positive
def bernsteinRow01 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 1 0 affine01753)
theorem bernsteinRow01_identity : bernsteinRow01=NestedInteger.coefficientFrom 88 1 0 affine01753 := by decide +kernel
theorem bernsteinRow01_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow01=true := by decide +kernel
#print axioms bernsteinRow01_identity
#print axioms bernsteinRow01_positive
def bernsteinRow02 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 2 0 affine01753)
theorem bernsteinRow02_identity : bernsteinRow02=NestedInteger.coefficientFrom 88 2 0 affine01753 := by decide +kernel
theorem bernsteinRow02_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow02=true := by decide +kernel
#print axioms bernsteinRow02_identity
#print axioms bernsteinRow02_positive
def bernsteinRow03 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 3 0 affine01753)
theorem bernsteinRow03_identity : bernsteinRow03=NestedInteger.coefficientFrom 88 3 0 affine01753 := by decide +kernel
theorem bernsteinRow03_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow03=true := by decide +kernel
#print axioms bernsteinRow03_identity
#print axioms bernsteinRow03_positive
def bernsteinRow04 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 4 0 affine01753)
theorem bernsteinRow04_identity : bernsteinRow04=NestedInteger.coefficientFrom 88 4 0 affine01753 := by decide +kernel
theorem bernsteinRow04_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow04=true := by decide +kernel
#print axioms bernsteinRow04_identity
#print axioms bernsteinRow04_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
