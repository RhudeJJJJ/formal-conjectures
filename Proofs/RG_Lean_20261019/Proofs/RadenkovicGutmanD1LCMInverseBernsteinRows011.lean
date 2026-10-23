/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow55 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 55 0 affine01753)
theorem bernsteinRow55_identity : bernsteinRow55=NestedInteger.coefficientFrom 88 55 0 affine01753 := by decide +kernel
theorem bernsteinRow55_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow55=true := by decide +kernel
#print axioms bernsteinRow55_identity
#print axioms bernsteinRow55_positive
def bernsteinRow56 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 56 0 affine01753)
theorem bernsteinRow56_identity : bernsteinRow56=NestedInteger.coefficientFrom 88 56 0 affine01753 := by decide +kernel
theorem bernsteinRow56_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow56=true := by decide +kernel
#print axioms bernsteinRow56_identity
#print axioms bernsteinRow56_positive
def bernsteinRow57 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 57 0 affine01753)
theorem bernsteinRow57_identity : bernsteinRow57=NestedInteger.coefficientFrom 88 57 0 affine01753 := by decide +kernel
theorem bernsteinRow57_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow57=true := by decide +kernel
#print axioms bernsteinRow57_identity
#print axioms bernsteinRow57_positive
def bernsteinRow58 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 58 0 affine01753)
theorem bernsteinRow58_identity : bernsteinRow58=NestedInteger.coefficientFrom 88 58 0 affine01753 := by decide +kernel
theorem bernsteinRow58_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow58=true := by decide +kernel
#print axioms bernsteinRow58_identity
#print axioms bernsteinRow58_positive
def bernsteinRow59 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 59 0 affine01753)
theorem bernsteinRow59_identity : bernsteinRow59=NestedInteger.coefficientFrom 88 59 0 affine01753 := by decide +kernel
theorem bernsteinRow59_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow59=true := by decide +kernel
#print axioms bernsteinRow59_identity
#print axioms bernsteinRow59_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
