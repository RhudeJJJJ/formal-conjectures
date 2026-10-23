/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages
def bernsteinRow65 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 65 0 affine01753)
theorem bernsteinRow65_identity : bernsteinRow65=NestedInteger.coefficientFrom 88 65 0 affine01753 := by decide +kernel
theorem bernsteinRow65_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow65=true := by decide +kernel
#print axioms bernsteinRow65_identity
#print axioms bernsteinRow65_positive
def bernsteinRow66 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 66 0 affine01753)
theorem bernsteinRow66_identity : bernsteinRow66=NestedInteger.coefficientFrom 88 66 0 affine01753 := by decide +kernel
theorem bernsteinRow66_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow66=true := by decide +kernel
#print axioms bernsteinRow66_identity
#print axioms bernsteinRow66_positive
def bernsteinRow67 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 67 0 affine01753)
theorem bernsteinRow67_identity : bernsteinRow67=NestedInteger.coefficientFrom 88 67 0 affine01753 := by decide +kernel
theorem bernsteinRow67_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow67=true := by decide +kernel
#print axioms bernsteinRow67_identity
#print axioms bernsteinRow67_positive
def bernsteinRow68 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 68 0 affine01753)
theorem bernsteinRow68_identity : bernsteinRow68=NestedInteger.coefficientFrom 88 68 0 affine01753 := by decide +kernel
theorem bernsteinRow68_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow68=true := by decide +kernel
#print axioms bernsteinRow68_identity
#print axioms bernsteinRow68_positive
def bernsteinRow69 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 69 0 affine01753)
theorem bernsteinRow69_identity : bernsteinRow69=NestedInteger.coefficientFrom 88 69 0 affine01753 := by decide +kernel
theorem bernsteinRow69_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow69=true := by decide +kernel
#print axioms bernsteinRow69_identity
#print axioms bernsteinRow69_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
