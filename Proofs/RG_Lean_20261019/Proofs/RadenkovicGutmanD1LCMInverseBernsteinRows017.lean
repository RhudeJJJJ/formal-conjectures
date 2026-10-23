/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow85 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 85 0 affine01753)
theorem bernsteinRow85_identity : bernsteinRow85=NestedInteger.coefficientFrom 88 85 0 affine01753 := by decide +kernel
theorem bernsteinRow85_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow85=true := by decide +kernel
#print axioms bernsteinRow85_identity
#print axioms bernsteinRow85_positive
def bernsteinRow86 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 86 0 affine01753)
theorem bernsteinRow86_identity : bernsteinRow86=NestedInteger.coefficientFrom 88 86 0 affine01753 := by decide +kernel
theorem bernsteinRow86_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow86=true := by decide +kernel
#print axioms bernsteinRow86_identity
#print axioms bernsteinRow86_positive
def bernsteinRow87 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 87 0 affine01753)
theorem bernsteinRow87_identity : bernsteinRow87=NestedInteger.coefficientFrom 88 87 0 affine01753 := by decide +kernel
theorem bernsteinRow87_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow87=true := by decide +kernel
#print axioms bernsteinRow87_identity
#print axioms bernsteinRow87_positive
def bernsteinRow88 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 88 0 affine01753)
theorem bernsteinRow88_identity : bernsteinRow88=NestedInteger.coefficientFrom 88 88 0 affine01753 := by decide +kernel
theorem bernsteinRow88_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow88=true := by decide +kernel
#print axioms bernsteinRow88_identity
#print axioms bernsteinRow88_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
