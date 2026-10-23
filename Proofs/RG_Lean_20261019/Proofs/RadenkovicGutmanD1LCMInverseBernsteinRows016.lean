/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow80 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 80 0 affine01753)
theorem bernsteinRow80_identity : bernsteinRow80=NestedInteger.coefficientFrom 88 80 0 affine01753 := by decide +kernel
theorem bernsteinRow80_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow80=true := by decide +kernel
#print axioms bernsteinRow80_identity
#print axioms bernsteinRow80_positive
def bernsteinRow81 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 81 0 affine01753)
theorem bernsteinRow81_identity : bernsteinRow81=NestedInteger.coefficientFrom 88 81 0 affine01753 := by decide +kernel
theorem bernsteinRow81_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow81=true := by decide +kernel
#print axioms bernsteinRow81_identity
#print axioms bernsteinRow81_positive
def bernsteinRow82 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 82 0 affine01753)
theorem bernsteinRow82_identity : bernsteinRow82=NestedInteger.coefficientFrom 88 82 0 affine01753 := by decide +kernel
theorem bernsteinRow82_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow82=true := by decide +kernel
#print axioms bernsteinRow82_identity
#print axioms bernsteinRow82_positive
def bernsteinRow83 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 83 0 affine01753)
theorem bernsteinRow83_identity : bernsteinRow83=NestedInteger.coefficientFrom 88 83 0 affine01753 := by decide +kernel
theorem bernsteinRow83_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow83=true := by decide +kernel
#print axioms bernsteinRow83_identity
#print axioms bernsteinRow83_positive
def bernsteinRow84 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 84 0 affine01753)
theorem bernsteinRow84_identity : bernsteinRow84=NestedInteger.coefficientFrom 88 84 0 affine01753 := by decide +kernel
theorem bernsteinRow84_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow84=true := by decide +kernel
#print axioms bernsteinRow84_identity
#print axioms bernsteinRow84_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
