/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow05 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 5 0 affine01753)
theorem bernsteinRow05_identity : bernsteinRow05=NestedInteger.coefficientFrom 88 5 0 affine01753 := by decide +kernel
theorem bernsteinRow05_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow05=true := by decide +kernel
#print axioms bernsteinRow05_identity
#print axioms bernsteinRow05_positive
def bernsteinRow06 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 6 0 affine01753)
theorem bernsteinRow06_identity : bernsteinRow06=NestedInteger.coefficientFrom 88 6 0 affine01753 := by decide +kernel
theorem bernsteinRow06_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow06=true := by decide +kernel
#print axioms bernsteinRow06_identity
#print axioms bernsteinRow06_positive
def bernsteinRow07 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 7 0 affine01753)
theorem bernsteinRow07_identity : bernsteinRow07=NestedInteger.coefficientFrom 88 7 0 affine01753 := by decide +kernel
theorem bernsteinRow07_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow07=true := by decide +kernel
#print axioms bernsteinRow07_identity
#print axioms bernsteinRow07_positive
def bernsteinRow08 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 8 0 affine01753)
theorem bernsteinRow08_identity : bernsteinRow08=NestedInteger.coefficientFrom 88 8 0 affine01753 := by decide +kernel
theorem bernsteinRow08_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow08=true := by decide +kernel
#print axioms bernsteinRow08_identity
#print axioms bernsteinRow08_positive
def bernsteinRow09 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 9 0 affine01753)
theorem bernsteinRow09_identity : bernsteinRow09=NestedInteger.coefficientFrom 88 9 0 affine01753 := by decide +kernel
theorem bernsteinRow09_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow09=true := by decide +kernel
#print axioms bernsteinRow09_identity
#print axioms bernsteinRow09_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
