/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairJoins02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row048 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01260_w_affine)
theorem leaf01260_w_row048_weighted : leaf01260_w_row048=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row048_identity : leaf01260_w_row048=NestedInteger.coefficientFrom 88 48 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 48 0 leaf01260_w_affine leaf01260_w_row048 IntegerBernsteinWeights88.row048 (IntegerBernsteinTable.checked (n := 2) 88 48 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row048 leaf01260_w_affine_length IntegerBernsteinWeights88.row048_identity) leaf01260_w_row048_weighted
theorem leaf01260_w_row048_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row048=true := by decide +kernel
#print axioms leaf01260_w_row048_weighted
#print axioms leaf01260_w_row048_identity
#print axioms leaf01260_w_row048_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row049 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01260_w_affine)
theorem leaf01260_w_row049_weighted : leaf01260_w_row049=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row049_identity : leaf01260_w_row049=NestedInteger.coefficientFrom 88 49 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 49 0 leaf01260_w_affine leaf01260_w_row049 IntegerBernsteinWeights88.row049 (IntegerBernsteinTable.checked (n := 2) 88 49 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row049 leaf01260_w_affine_length IntegerBernsteinWeights88.row049_identity) leaf01260_w_row049_weighted
theorem leaf01260_w_row049_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row049=true := by decide +kernel
#print axioms leaf01260_w_row049_weighted
#print axioms leaf01260_w_row049_identity
#print axioms leaf01260_w_row049_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row050 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01260_w_affine)
theorem leaf01260_w_row050_weighted : leaf01260_w_row050=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row050_identity : leaf01260_w_row050=NestedInteger.coefficientFrom 88 50 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 50 0 leaf01260_w_affine leaf01260_w_row050 IntegerBernsteinWeights88.row050 (IntegerBernsteinTable.checked (n := 2) 88 50 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row050 leaf01260_w_affine_length IntegerBernsteinWeights88.row050_identity) leaf01260_w_row050_weighted
theorem leaf01260_w_row050_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row050=true := by decide +kernel
#print axioms leaf01260_w_row050_weighted
#print axioms leaf01260_w_row050_identity
#print axioms leaf01260_w_row050_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row051 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01260_w_affine)
theorem leaf01260_w_row051_weighted : leaf01260_w_row051=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row051_identity : leaf01260_w_row051=NestedInteger.coefficientFrom 88 51 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 51 0 leaf01260_w_affine leaf01260_w_row051 IntegerBernsteinWeights88.row051 (IntegerBernsteinTable.checked (n := 2) 88 51 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row051 leaf01260_w_affine_length IntegerBernsteinWeights88.row051_identity) leaf01260_w_row051_weighted
theorem leaf01260_w_row051_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row051=true := by decide +kernel
#print axioms leaf01260_w_row051_weighted
#print axioms leaf01260_w_row051_identity
#print axioms leaf01260_w_row051_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row052 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01260_w_affine)
theorem leaf01260_w_row052_weighted : leaf01260_w_row052=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row052_identity : leaf01260_w_row052=NestedInteger.coefficientFrom 88 52 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 52 0 leaf01260_w_affine leaf01260_w_row052 IntegerBernsteinWeights88.row052 (IntegerBernsteinTable.checked (n := 2) 88 52 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row052 leaf01260_w_affine_length IntegerBernsteinWeights88.row052_identity) leaf01260_w_row052_weighted
theorem leaf01260_w_row052_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row052=true := by decide +kernel
#print axioms leaf01260_w_row052_weighted
#print axioms leaf01260_w_row052_identity
#print axioms leaf01260_w_row052_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row053 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01260_w_affine)
theorem leaf01260_w_row053_weighted : leaf01260_w_row053=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row053_identity : leaf01260_w_row053=NestedInteger.coefficientFrom 88 53 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 53 0 leaf01260_w_affine leaf01260_w_row053 IntegerBernsteinWeights88.row053 (IntegerBernsteinTable.checked (n := 2) 88 53 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row053 leaf01260_w_affine_length IntegerBernsteinWeights88.row053_identity) leaf01260_w_row053_weighted
theorem leaf01260_w_row053_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row053=true := by decide +kernel
#print axioms leaf01260_w_row053_weighted
#print axioms leaf01260_w_row053_identity
#print axioms leaf01260_w_row053_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row054 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01260_w_affine)
theorem leaf01260_w_row054_weighted : leaf01260_w_row054=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row054_identity : leaf01260_w_row054=NestedInteger.coefficientFrom 88 54 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 54 0 leaf01260_w_affine leaf01260_w_row054 IntegerBernsteinWeights88.row054 (IntegerBernsteinTable.checked (n := 2) 88 54 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row054 leaf01260_w_affine_length IntegerBernsteinWeights88.row054_identity) leaf01260_w_row054_weighted
theorem leaf01260_w_row054_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row054=true := by decide +kernel
#print axioms leaf01260_w_row054_weighted
#print axioms leaf01260_w_row054_identity
#print axioms leaf01260_w_row054_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row055 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01260_w_affine)
theorem leaf01260_w_row055_weighted : leaf01260_w_row055=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row055_identity : leaf01260_w_row055=NestedInteger.coefficientFrom 88 55 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 55 0 leaf01260_w_affine leaf01260_w_row055 IntegerBernsteinWeights88.row055 (IntegerBernsteinTable.checked (n := 2) 88 55 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row055 leaf01260_w_affine_length IntegerBernsteinWeights88.row055_identity) leaf01260_w_row055_weighted
theorem leaf01260_w_row055_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row055=true := by decide +kernel
#print axioms leaf01260_w_row055_weighted
#print axioms leaf01260_w_row055_identity
#print axioms leaf01260_w_row055_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row056 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01260_w_affine)
theorem leaf01260_w_row056_weighted : leaf01260_w_row056=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row056_identity : leaf01260_w_row056=NestedInteger.coefficientFrom 88 56 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 56 0 leaf01260_w_affine leaf01260_w_row056 IntegerBernsteinWeights88.row056 (IntegerBernsteinTable.checked (n := 2) 88 56 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row056 leaf01260_w_affine_length IntegerBernsteinWeights88.row056_identity) leaf01260_w_row056_weighted
theorem leaf01260_w_row056_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row056=true := by decide +kernel
#print axioms leaf01260_w_row056_weighted
#print axioms leaf01260_w_row056_identity
#print axioms leaf01260_w_row056_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row057 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01260_w_affine)
theorem leaf01260_w_row057_weighted : leaf01260_w_row057=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row057_identity : leaf01260_w_row057=NestedInteger.coefficientFrom 88 57 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 57 0 leaf01260_w_affine leaf01260_w_row057 IntegerBernsteinWeights88.row057 (IntegerBernsteinTable.checked (n := 2) 88 57 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row057 leaf01260_w_affine_length IntegerBernsteinWeights88.row057_identity) leaf01260_w_row057_weighted
theorem leaf01260_w_row057_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row057=true := by decide +kernel
#print axioms leaf01260_w_row057_weighted
#print axioms leaf01260_w_row057_identity
#print axioms leaf01260_w_row057_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row058 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01260_w_affine)
theorem leaf01260_w_row058_weighted : leaf01260_w_row058=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row058_identity : leaf01260_w_row058=NestedInteger.coefficientFrom 88 58 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 58 0 leaf01260_w_affine leaf01260_w_row058 IntegerBernsteinWeights88.row058 (IntegerBernsteinTable.checked (n := 2) 88 58 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row058 leaf01260_w_affine_length IntegerBernsteinWeights88.row058_identity) leaf01260_w_row058_weighted
theorem leaf01260_w_row058_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row058=true := by decide +kernel
#print axioms leaf01260_w_row058_weighted
#print axioms leaf01260_w_row058_identity
#print axioms leaf01260_w_row058_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row059 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01260_w_affine)
theorem leaf01260_w_row059_weighted : leaf01260_w_row059=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row059_identity : leaf01260_w_row059=NestedInteger.coefficientFrom 88 59 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 59 0 leaf01260_w_affine leaf01260_w_row059 IntegerBernsteinWeights88.row059 (IntegerBernsteinTable.checked (n := 2) 88 59 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row059 leaf01260_w_affine_length IntegerBernsteinWeights88.row059_identity) leaf01260_w_row059_weighted
theorem leaf01260_w_row059_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row059=true := by decide +kernel
#print axioms leaf01260_w_row059_weighted
#print axioms leaf01260_w_row059_identity
#print axioms leaf01260_w_row059_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row060 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01260_w_affine)
theorem leaf01260_w_row060_weighted : leaf01260_w_row060=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row060_identity : leaf01260_w_row060=NestedInteger.coefficientFrom 88 60 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 60 0 leaf01260_w_affine leaf01260_w_row060 IntegerBernsteinWeights88.row060 (IntegerBernsteinTable.checked (n := 2) 88 60 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row060 leaf01260_w_affine_length IntegerBernsteinWeights88.row060_identity) leaf01260_w_row060_weighted
theorem leaf01260_w_row060_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row060=true := by decide +kernel
#print axioms leaf01260_w_row060_weighted
#print axioms leaf01260_w_row060_identity
#print axioms leaf01260_w_row060_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row061 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01260_w_affine)
theorem leaf01260_w_row061_weighted : leaf01260_w_row061=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row061_identity : leaf01260_w_row061=NestedInteger.coefficientFrom 88 61 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 61 0 leaf01260_w_affine leaf01260_w_row061 IntegerBernsteinWeights88.row061 (IntegerBernsteinTable.checked (n := 2) 88 61 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row061 leaf01260_w_affine_length IntegerBernsteinWeights88.row061_identity) leaf01260_w_row061_weighted
theorem leaf01260_w_row061_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row061=true := by decide +kernel
#print axioms leaf01260_w_row061_weighted
#print axioms leaf01260_w_row061_identity
#print axioms leaf01260_w_row061_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row062 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01260_w_affine)
theorem leaf01260_w_row062_weighted : leaf01260_w_row062=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row062_identity : leaf01260_w_row062=NestedInteger.coefficientFrom 88 62 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 62 0 leaf01260_w_affine leaf01260_w_row062 IntegerBernsteinWeights88.row062 (IntegerBernsteinTable.checked (n := 2) 88 62 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row062 leaf01260_w_affine_length IntegerBernsteinWeights88.row062_identity) leaf01260_w_row062_weighted
theorem leaf01260_w_row062_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row062=true := by decide +kernel
#print axioms leaf01260_w_row062_weighted
#print axioms leaf01260_w_row062_identity
#print axioms leaf01260_w_row062_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row063 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01260_w_affine)
theorem leaf01260_w_row063_weighted : leaf01260_w_row063=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row063_identity : leaf01260_w_row063=NestedInteger.coefficientFrom 88 63 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 63 0 leaf01260_w_affine leaf01260_w_row063 IntegerBernsteinWeights88.row063 (IntegerBernsteinTable.checked (n := 2) 88 63 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row063 leaf01260_w_affine_length IntegerBernsteinWeights88.row063_identity) leaf01260_w_row063_weighted
theorem leaf01260_w_row063_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row063=true := by decide +kernel
#print axioms leaf01260_w_row063_weighted
#print axioms leaf01260_w_row063_identity
#print axioms leaf01260_w_row063_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
