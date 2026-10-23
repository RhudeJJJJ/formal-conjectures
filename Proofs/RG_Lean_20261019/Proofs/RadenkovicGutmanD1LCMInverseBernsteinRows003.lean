/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinRow15 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 15 0 affine01753)
theorem bernsteinRow15_identity : bernsteinRow15=NestedInteger.coefficientFrom 88 15 0 affine01753 := by decide +kernel
theorem bernsteinRow15_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow15=true := by decide +kernel
#print axioms bernsteinRow15_identity
#print axioms bernsteinRow15_positive
def bernsteinRow16 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 16 0 affine01753)
theorem bernsteinRow16_identity : bernsteinRow16=NestedInteger.coefficientFrom 88 16 0 affine01753 := by decide +kernel
theorem bernsteinRow16_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow16=true := by decide +kernel
#print axioms bernsteinRow16_identity
#print axioms bernsteinRow16_positive
def bernsteinRow17 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 17 0 affine01753)
theorem bernsteinRow17_identity : bernsteinRow17=NestedInteger.coefficientFrom 88 17 0 affine01753 := by decide +kernel
theorem bernsteinRow17_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow17=true := by decide +kernel
#print axioms bernsteinRow17_identity
#print axioms bernsteinRow17_positive
def bernsteinRow18 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 18 0 affine01753)
theorem bernsteinRow18_identity : bernsteinRow18=NestedInteger.coefficientFrom 88 18 0 affine01753 := by decide +kernel
theorem bernsteinRow18_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow18=true := by decide +kernel
#print axioms bernsteinRow18_identity
#print axioms bernsteinRow18_positive
def bernsteinRow19 : NestedInteger.Poly 2 := rg_integer_row%
  (NestedInteger.coefficientFrom 88 19 0 affine01753)
theorem bernsteinRow19_identity : bernsteinRow19=NestedInteger.coefficientFrom 88 19 0 affine01753 := by decide +kernel
theorem bernsteinRow19_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow19=true := by decide +kernel
#print axioms bernsteinRow19_identity
#print axioms bernsteinRow19_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
