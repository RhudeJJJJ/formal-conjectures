/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow20 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 20 0 affine01753)
theorem bernsteinRow20_identity : bernsteinRow20=NestedInteger.coefficientFrom 88 20 0 affine01753 := by decide +kernel
theorem bernsteinRow20_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow20=true := by decide +kernel
#print axioms bernsteinRow20_identity
#print axioms bernsteinRow20_positive
def bernsteinRow21 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 21 0 affine01753)
theorem bernsteinRow21_identity : bernsteinRow21=NestedInteger.coefficientFrom 88 21 0 affine01753 := by decide +kernel
theorem bernsteinRow21_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow21=true := by decide +kernel
#print axioms bernsteinRow21_identity
#print axioms bernsteinRow21_positive
def bernsteinRow22 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 22 0 affine01753)
theorem bernsteinRow22_identity : bernsteinRow22=NestedInteger.coefficientFrom 88 22 0 affine01753 := by decide +kernel
theorem bernsteinRow22_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow22=true := by decide +kernel
#print axioms bernsteinRow22_identity
#print axioms bernsteinRow22_positive
def bernsteinRow23 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 23 0 affine01753)
theorem bernsteinRow23_identity : bernsteinRow23=NestedInteger.coefficientFrom 88 23 0 affine01753 := by decide +kernel
theorem bernsteinRow23_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow23=true := by decide +kernel
#print axioms bernsteinRow23_identity
#print axioms bernsteinRow23_positive
def bernsteinRow24 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 24 0 affine01753)
theorem bernsteinRow24_identity : bernsteinRow24=NestedInteger.coefficientFrom 88 24 0 affine01753 := by decide +kernel
theorem bernsteinRow24_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow24=true := by decide +kernel
#print axioms bernsteinRow24_identity
#print axioms bernsteinRow24_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
