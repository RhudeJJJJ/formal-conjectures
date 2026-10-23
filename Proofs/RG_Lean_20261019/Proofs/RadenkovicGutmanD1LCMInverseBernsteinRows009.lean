/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow45 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 45 0 affine01753)
theorem bernsteinRow45_identity : bernsteinRow45=NestedInteger.coefficientFrom 88 45 0 affine01753 := by decide +kernel
theorem bernsteinRow45_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow45=true := by decide +kernel
#print axioms bernsteinRow45_identity
#print axioms bernsteinRow45_positive
def bernsteinRow46 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 46 0 affine01753)
theorem bernsteinRow46_identity : bernsteinRow46=NestedInteger.coefficientFrom 88 46 0 affine01753 := by decide +kernel
theorem bernsteinRow46_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow46=true := by decide +kernel
#print axioms bernsteinRow46_identity
#print axioms bernsteinRow46_positive
def bernsteinRow47 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 47 0 affine01753)
theorem bernsteinRow47_identity : bernsteinRow47=NestedInteger.coefficientFrom 88 47 0 affine01753 := by decide +kernel
theorem bernsteinRow47_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow47=true := by decide +kernel
#print axioms bernsteinRow47_identity
#print axioms bernsteinRow47_positive
def bernsteinRow48 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 48 0 affine01753)
theorem bernsteinRow48_identity : bernsteinRow48=NestedInteger.coefficientFrom 88 48 0 affine01753 := by decide +kernel
theorem bernsteinRow48_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow48=true := by decide +kernel
#print axioms bernsteinRow48_identity
#print axioms bernsteinRow48_positive
def bernsteinRow49 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 49 0 affine01753)
theorem bernsteinRow49_identity : bernsteinRow49=NestedInteger.coefficientFrom 88 49 0 affine01753 := by decide +kernel
theorem bernsteinRow49_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow49=true := by decide +kernel
#print axioms bernsteinRow49_identity
#print axioms bernsteinRow49_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
