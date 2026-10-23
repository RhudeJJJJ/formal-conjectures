/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow30 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 30 0 affine01753)
theorem bernsteinRow30_identity : bernsteinRow30=NestedInteger.coefficientFrom 88 30 0 affine01753 := by decide +kernel
theorem bernsteinRow30_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow30=true := by decide +kernel
#print axioms bernsteinRow30_identity
#print axioms bernsteinRow30_positive
def bernsteinRow31 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 31 0 affine01753)
theorem bernsteinRow31_identity : bernsteinRow31=NestedInteger.coefficientFrom 88 31 0 affine01753 := by decide +kernel
theorem bernsteinRow31_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow31=true := by decide +kernel
#print axioms bernsteinRow31_identity
#print axioms bernsteinRow31_positive
def bernsteinRow32 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 32 0 affine01753)
theorem bernsteinRow32_identity : bernsteinRow32=NestedInteger.coefficientFrom 88 32 0 affine01753 := by decide +kernel
theorem bernsteinRow32_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow32=true := by decide +kernel
#print axioms bernsteinRow32_identity
#print axioms bernsteinRow32_positive
def bernsteinRow33 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 33 0 affine01753)
theorem bernsteinRow33_identity : bernsteinRow33=NestedInteger.coefficientFrom 88 33 0 affine01753 := by decide +kernel
theorem bernsteinRow33_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow33=true := by decide +kernel
#print axioms bernsteinRow33_identity
#print axioms bernsteinRow33_positive
def bernsteinRow34 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 34 0 affine01753)
theorem bernsteinRow34_identity : bernsteinRow34=NestedInteger.coefficientFrom 88 34 0 affine01753 := by decide +kernel
theorem bernsteinRow34_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow34=true := by decide +kernel
#print axioms bernsteinRow34_identity
#print axioms bernsteinRow34_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
