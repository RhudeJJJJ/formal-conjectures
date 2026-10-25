/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairJoins02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row032 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01260_w_affine)
theorem leaf01260_w_row032_weighted : leaf01260_w_row032=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row032_identity : leaf01260_w_row032=NestedInteger.coefficientFrom 88 32 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 32 0 leaf01260_w_affine leaf01260_w_row032 IntegerBernsteinWeights88.row032 (IntegerBernsteinTable.checked (n := 2) 88 32 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row032 leaf01260_w_affine_length IntegerBernsteinWeights88.row032_identity) leaf01260_w_row032_weighted
theorem leaf01260_w_row032_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row032=true := by decide +kernel
#print axioms leaf01260_w_row032_weighted
#print axioms leaf01260_w_row032_identity
#print axioms leaf01260_w_row032_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row033 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01260_w_affine)
theorem leaf01260_w_row033_weighted : leaf01260_w_row033=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row033_identity : leaf01260_w_row033=NestedInteger.coefficientFrom 88 33 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 33 0 leaf01260_w_affine leaf01260_w_row033 IntegerBernsteinWeights88.row033 (IntegerBernsteinTable.checked (n := 2) 88 33 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row033 leaf01260_w_affine_length IntegerBernsteinWeights88.row033_identity) leaf01260_w_row033_weighted
theorem leaf01260_w_row033_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row033=true := by decide +kernel
#print axioms leaf01260_w_row033_weighted
#print axioms leaf01260_w_row033_identity
#print axioms leaf01260_w_row033_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row034 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01260_w_affine)
theorem leaf01260_w_row034_weighted : leaf01260_w_row034=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row034_identity : leaf01260_w_row034=NestedInteger.coefficientFrom 88 34 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 34 0 leaf01260_w_affine leaf01260_w_row034 IntegerBernsteinWeights88.row034 (IntegerBernsteinTable.checked (n := 2) 88 34 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row034 leaf01260_w_affine_length IntegerBernsteinWeights88.row034_identity) leaf01260_w_row034_weighted
theorem leaf01260_w_row034_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row034=true := by decide +kernel
#print axioms leaf01260_w_row034_weighted
#print axioms leaf01260_w_row034_identity
#print axioms leaf01260_w_row034_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row035 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01260_w_affine)
theorem leaf01260_w_row035_weighted : leaf01260_w_row035=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row035_identity : leaf01260_w_row035=NestedInteger.coefficientFrom 88 35 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 35 0 leaf01260_w_affine leaf01260_w_row035 IntegerBernsteinWeights88.row035 (IntegerBernsteinTable.checked (n := 2) 88 35 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row035 leaf01260_w_affine_length IntegerBernsteinWeights88.row035_identity) leaf01260_w_row035_weighted
theorem leaf01260_w_row035_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row035=true := by decide +kernel
#print axioms leaf01260_w_row035_weighted
#print axioms leaf01260_w_row035_identity
#print axioms leaf01260_w_row035_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row036 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01260_w_affine)
theorem leaf01260_w_row036_weighted : leaf01260_w_row036=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row036_identity : leaf01260_w_row036=NestedInteger.coefficientFrom 88 36 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 36 0 leaf01260_w_affine leaf01260_w_row036 IntegerBernsteinWeights88.row036 (IntegerBernsteinTable.checked (n := 2) 88 36 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row036 leaf01260_w_affine_length IntegerBernsteinWeights88.row036_identity) leaf01260_w_row036_weighted
theorem leaf01260_w_row036_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row036=true := by decide +kernel
#print axioms leaf01260_w_row036_weighted
#print axioms leaf01260_w_row036_identity
#print axioms leaf01260_w_row036_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row037 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01260_w_affine)
theorem leaf01260_w_row037_weighted : leaf01260_w_row037=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row037_identity : leaf01260_w_row037=NestedInteger.coefficientFrom 88 37 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 37 0 leaf01260_w_affine leaf01260_w_row037 IntegerBernsteinWeights88.row037 (IntegerBernsteinTable.checked (n := 2) 88 37 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row037 leaf01260_w_affine_length IntegerBernsteinWeights88.row037_identity) leaf01260_w_row037_weighted
theorem leaf01260_w_row037_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row037=true := by decide +kernel
#print axioms leaf01260_w_row037_weighted
#print axioms leaf01260_w_row037_identity
#print axioms leaf01260_w_row037_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row038 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01260_w_affine)
theorem leaf01260_w_row038_weighted : leaf01260_w_row038=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row038_identity : leaf01260_w_row038=NestedInteger.coefficientFrom 88 38 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 38 0 leaf01260_w_affine leaf01260_w_row038 IntegerBernsteinWeights88.row038 (IntegerBernsteinTable.checked (n := 2) 88 38 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row038 leaf01260_w_affine_length IntegerBernsteinWeights88.row038_identity) leaf01260_w_row038_weighted
theorem leaf01260_w_row038_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row038=true := by decide +kernel
#print axioms leaf01260_w_row038_weighted
#print axioms leaf01260_w_row038_identity
#print axioms leaf01260_w_row038_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row039 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01260_w_affine)
theorem leaf01260_w_row039_weighted : leaf01260_w_row039=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row039_identity : leaf01260_w_row039=NestedInteger.coefficientFrom 88 39 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 39 0 leaf01260_w_affine leaf01260_w_row039 IntegerBernsteinWeights88.row039 (IntegerBernsteinTable.checked (n := 2) 88 39 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row039 leaf01260_w_affine_length IntegerBernsteinWeights88.row039_identity) leaf01260_w_row039_weighted
theorem leaf01260_w_row039_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row039=true := by decide +kernel
#print axioms leaf01260_w_row039_weighted
#print axioms leaf01260_w_row039_identity
#print axioms leaf01260_w_row039_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row040 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01260_w_affine)
theorem leaf01260_w_row040_weighted : leaf01260_w_row040=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row040_identity : leaf01260_w_row040=NestedInteger.coefficientFrom 88 40 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 40 0 leaf01260_w_affine leaf01260_w_row040 IntegerBernsteinWeights88.row040 (IntegerBernsteinTable.checked (n := 2) 88 40 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row040 leaf01260_w_affine_length IntegerBernsteinWeights88.row040_identity) leaf01260_w_row040_weighted
theorem leaf01260_w_row040_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row040=true := by decide +kernel
#print axioms leaf01260_w_row040_weighted
#print axioms leaf01260_w_row040_identity
#print axioms leaf01260_w_row040_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row041 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01260_w_affine)
theorem leaf01260_w_row041_weighted : leaf01260_w_row041=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row041_identity : leaf01260_w_row041=NestedInteger.coefficientFrom 88 41 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 41 0 leaf01260_w_affine leaf01260_w_row041 IntegerBernsteinWeights88.row041 (IntegerBernsteinTable.checked (n := 2) 88 41 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row041 leaf01260_w_affine_length IntegerBernsteinWeights88.row041_identity) leaf01260_w_row041_weighted
theorem leaf01260_w_row041_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row041=true := by decide +kernel
#print axioms leaf01260_w_row041_weighted
#print axioms leaf01260_w_row041_identity
#print axioms leaf01260_w_row041_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row042 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01260_w_affine)
theorem leaf01260_w_row042_weighted : leaf01260_w_row042=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row042_identity : leaf01260_w_row042=NestedInteger.coefficientFrom 88 42 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 42 0 leaf01260_w_affine leaf01260_w_row042 IntegerBernsteinWeights88.row042 (IntegerBernsteinTable.checked (n := 2) 88 42 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row042 leaf01260_w_affine_length IntegerBernsteinWeights88.row042_identity) leaf01260_w_row042_weighted
theorem leaf01260_w_row042_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row042=true := by decide +kernel
#print axioms leaf01260_w_row042_weighted
#print axioms leaf01260_w_row042_identity
#print axioms leaf01260_w_row042_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row043 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01260_w_affine)
theorem leaf01260_w_row043_weighted : leaf01260_w_row043=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row043_identity : leaf01260_w_row043=NestedInteger.coefficientFrom 88 43 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 43 0 leaf01260_w_affine leaf01260_w_row043 IntegerBernsteinWeights88.row043 (IntegerBernsteinTable.checked (n := 2) 88 43 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row043 leaf01260_w_affine_length IntegerBernsteinWeights88.row043_identity) leaf01260_w_row043_weighted
theorem leaf01260_w_row043_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row043=true := by decide +kernel
#print axioms leaf01260_w_row043_weighted
#print axioms leaf01260_w_row043_identity
#print axioms leaf01260_w_row043_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row044 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01260_w_affine)
theorem leaf01260_w_row044_weighted : leaf01260_w_row044=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row044_identity : leaf01260_w_row044=NestedInteger.coefficientFrom 88 44 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 44 0 leaf01260_w_affine leaf01260_w_row044 IntegerBernsteinWeights88.row044 (IntegerBernsteinTable.checked (n := 2) 88 44 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row044 leaf01260_w_affine_length IntegerBernsteinWeights88.row044_identity) leaf01260_w_row044_weighted
theorem leaf01260_w_row044_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row044=true := by decide +kernel
#print axioms leaf01260_w_row044_weighted
#print axioms leaf01260_w_row044_identity
#print axioms leaf01260_w_row044_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row045 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01260_w_affine)
theorem leaf01260_w_row045_weighted : leaf01260_w_row045=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row045_identity : leaf01260_w_row045=NestedInteger.coefficientFrom 88 45 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 45 0 leaf01260_w_affine leaf01260_w_row045 IntegerBernsteinWeights88.row045 (IntegerBernsteinTable.checked (n := 2) 88 45 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row045 leaf01260_w_affine_length IntegerBernsteinWeights88.row045_identity) leaf01260_w_row045_weighted
theorem leaf01260_w_row045_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row045=true := by decide +kernel
#print axioms leaf01260_w_row045_weighted
#print axioms leaf01260_w_row045_identity
#print axioms leaf01260_w_row045_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row046 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01260_w_affine)
theorem leaf01260_w_row046_weighted : leaf01260_w_row046=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row046_identity : leaf01260_w_row046=NestedInteger.coefficientFrom 88 46 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 46 0 leaf01260_w_affine leaf01260_w_row046 IntegerBernsteinWeights88.row046 (IntegerBernsteinTable.checked (n := 2) 88 46 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row046 leaf01260_w_affine_length IntegerBernsteinWeights88.row046_identity) leaf01260_w_row046_weighted
theorem leaf01260_w_row046_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row046=true := by decide +kernel
#print axioms leaf01260_w_row046_weighted
#print axioms leaf01260_w_row046_identity
#print axioms leaf01260_w_row046_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row047 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01260_w_affine)
theorem leaf01260_w_row047_weighted : leaf01260_w_row047=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row047_identity : leaf01260_w_row047=NestedInteger.coefficientFrom 88 47 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 47 0 leaf01260_w_affine leaf01260_w_row047 IntegerBernsteinWeights88.row047 (IntegerBernsteinTable.checked (n := 2) 88 47 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row047 leaf01260_w_affine_length IntegerBernsteinWeights88.row047_identity) leaf01260_w_row047_weighted
theorem leaf01260_w_row047_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row047=true := by decide +kernel
#print axioms leaf01260_w_row047_weighted
#print axioms leaf01260_w_row047_identity
#print axioms leaf01260_w_row047_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
