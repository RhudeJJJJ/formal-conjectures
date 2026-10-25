/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairJoins02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row000 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01260_w_affine)
theorem leaf01260_w_row000_weighted : leaf01260_w_row000=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row000_identity : leaf01260_w_row000=NestedInteger.coefficientFrom 88 0 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 0 0 leaf01260_w_affine leaf01260_w_row000 IntegerBernsteinWeights88.row000 (IntegerBernsteinTable.checked (n := 2) 88 0 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row000 leaf01260_w_affine_length IntegerBernsteinWeights88.row000_identity) leaf01260_w_row000_weighted
theorem leaf01260_w_row000_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row000=true := by decide +kernel
#print axioms leaf01260_w_row000_weighted
#print axioms leaf01260_w_row000_identity
#print axioms leaf01260_w_row000_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row001 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01260_w_affine)
theorem leaf01260_w_row001_weighted : leaf01260_w_row001=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row001_identity : leaf01260_w_row001=NestedInteger.coefficientFrom 88 1 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 1 0 leaf01260_w_affine leaf01260_w_row001 IntegerBernsteinWeights88.row001 (IntegerBernsteinTable.checked (n := 2) 88 1 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row001 leaf01260_w_affine_length IntegerBernsteinWeights88.row001_identity) leaf01260_w_row001_weighted
theorem leaf01260_w_row001_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row001=true := by decide +kernel
#print axioms leaf01260_w_row001_weighted
#print axioms leaf01260_w_row001_identity
#print axioms leaf01260_w_row001_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row002 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01260_w_affine)
theorem leaf01260_w_row002_weighted : leaf01260_w_row002=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row002_identity : leaf01260_w_row002=NestedInteger.coefficientFrom 88 2 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 2 0 leaf01260_w_affine leaf01260_w_row002 IntegerBernsteinWeights88.row002 (IntegerBernsteinTable.checked (n := 2) 88 2 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row002 leaf01260_w_affine_length IntegerBernsteinWeights88.row002_identity) leaf01260_w_row002_weighted
theorem leaf01260_w_row002_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row002=true := by decide +kernel
#print axioms leaf01260_w_row002_weighted
#print axioms leaf01260_w_row002_identity
#print axioms leaf01260_w_row002_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row003 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01260_w_affine)
theorem leaf01260_w_row003_weighted : leaf01260_w_row003=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row003_identity : leaf01260_w_row003=NestedInteger.coefficientFrom 88 3 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 3 0 leaf01260_w_affine leaf01260_w_row003 IntegerBernsteinWeights88.row003 (IntegerBernsteinTable.checked (n := 2) 88 3 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row003 leaf01260_w_affine_length IntegerBernsteinWeights88.row003_identity) leaf01260_w_row003_weighted
theorem leaf01260_w_row003_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row003=true := by decide +kernel
#print axioms leaf01260_w_row003_weighted
#print axioms leaf01260_w_row003_identity
#print axioms leaf01260_w_row003_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row004 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01260_w_affine)
theorem leaf01260_w_row004_weighted : leaf01260_w_row004=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row004_identity : leaf01260_w_row004=NestedInteger.coefficientFrom 88 4 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 4 0 leaf01260_w_affine leaf01260_w_row004 IntegerBernsteinWeights88.row004 (IntegerBernsteinTable.checked (n := 2) 88 4 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row004 leaf01260_w_affine_length IntegerBernsteinWeights88.row004_identity) leaf01260_w_row004_weighted
theorem leaf01260_w_row004_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row004=true := by decide +kernel
#print axioms leaf01260_w_row004_weighted
#print axioms leaf01260_w_row004_identity
#print axioms leaf01260_w_row004_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row005 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01260_w_affine)
theorem leaf01260_w_row005_weighted : leaf01260_w_row005=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row005_identity : leaf01260_w_row005=NestedInteger.coefficientFrom 88 5 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 5 0 leaf01260_w_affine leaf01260_w_row005 IntegerBernsteinWeights88.row005 (IntegerBernsteinTable.checked (n := 2) 88 5 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row005 leaf01260_w_affine_length IntegerBernsteinWeights88.row005_identity) leaf01260_w_row005_weighted
theorem leaf01260_w_row005_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row005=true := by decide +kernel
#print axioms leaf01260_w_row005_weighted
#print axioms leaf01260_w_row005_identity
#print axioms leaf01260_w_row005_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row006 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01260_w_affine)
theorem leaf01260_w_row006_weighted : leaf01260_w_row006=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row006_identity : leaf01260_w_row006=NestedInteger.coefficientFrom 88 6 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 6 0 leaf01260_w_affine leaf01260_w_row006 IntegerBernsteinWeights88.row006 (IntegerBernsteinTable.checked (n := 2) 88 6 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row006 leaf01260_w_affine_length IntegerBernsteinWeights88.row006_identity) leaf01260_w_row006_weighted
theorem leaf01260_w_row006_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row006=true := by decide +kernel
#print axioms leaf01260_w_row006_weighted
#print axioms leaf01260_w_row006_identity
#print axioms leaf01260_w_row006_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row007 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01260_w_affine)
theorem leaf01260_w_row007_weighted : leaf01260_w_row007=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row007_identity : leaf01260_w_row007=NestedInteger.coefficientFrom 88 7 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 7 0 leaf01260_w_affine leaf01260_w_row007 IntegerBernsteinWeights88.row007 (IntegerBernsteinTable.checked (n := 2) 88 7 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row007 leaf01260_w_affine_length IntegerBernsteinWeights88.row007_identity) leaf01260_w_row007_weighted
theorem leaf01260_w_row007_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row007=true := by decide +kernel
#print axioms leaf01260_w_row007_weighted
#print axioms leaf01260_w_row007_identity
#print axioms leaf01260_w_row007_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row008 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01260_w_affine)
theorem leaf01260_w_row008_weighted : leaf01260_w_row008=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row008_identity : leaf01260_w_row008=NestedInteger.coefficientFrom 88 8 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 8 0 leaf01260_w_affine leaf01260_w_row008 IntegerBernsteinWeights88.row008 (IntegerBernsteinTable.checked (n := 2) 88 8 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row008 leaf01260_w_affine_length IntegerBernsteinWeights88.row008_identity) leaf01260_w_row008_weighted
theorem leaf01260_w_row008_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row008=true := by decide +kernel
#print axioms leaf01260_w_row008_weighted
#print axioms leaf01260_w_row008_identity
#print axioms leaf01260_w_row008_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row009 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01260_w_affine)
theorem leaf01260_w_row009_weighted : leaf01260_w_row009=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row009_identity : leaf01260_w_row009=NestedInteger.coefficientFrom 88 9 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 9 0 leaf01260_w_affine leaf01260_w_row009 IntegerBernsteinWeights88.row009 (IntegerBernsteinTable.checked (n := 2) 88 9 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row009 leaf01260_w_affine_length IntegerBernsteinWeights88.row009_identity) leaf01260_w_row009_weighted
theorem leaf01260_w_row009_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row009=true := by decide +kernel
#print axioms leaf01260_w_row009_weighted
#print axioms leaf01260_w_row009_identity
#print axioms leaf01260_w_row009_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row010 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01260_w_affine)
theorem leaf01260_w_row010_weighted : leaf01260_w_row010=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row010_identity : leaf01260_w_row010=NestedInteger.coefficientFrom 88 10 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 10 0 leaf01260_w_affine leaf01260_w_row010 IntegerBernsteinWeights88.row010 (IntegerBernsteinTable.checked (n := 2) 88 10 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row010 leaf01260_w_affine_length IntegerBernsteinWeights88.row010_identity) leaf01260_w_row010_weighted
theorem leaf01260_w_row010_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row010=true := by decide +kernel
#print axioms leaf01260_w_row010_weighted
#print axioms leaf01260_w_row010_identity
#print axioms leaf01260_w_row010_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row011 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01260_w_affine)
theorem leaf01260_w_row011_weighted : leaf01260_w_row011=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row011_identity : leaf01260_w_row011=NestedInteger.coefficientFrom 88 11 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 11 0 leaf01260_w_affine leaf01260_w_row011 IntegerBernsteinWeights88.row011 (IntegerBernsteinTable.checked (n := 2) 88 11 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row011 leaf01260_w_affine_length IntegerBernsteinWeights88.row011_identity) leaf01260_w_row011_weighted
theorem leaf01260_w_row011_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row011=true := by decide +kernel
#print axioms leaf01260_w_row011_weighted
#print axioms leaf01260_w_row011_identity
#print axioms leaf01260_w_row011_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row012 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01260_w_affine)
theorem leaf01260_w_row012_weighted : leaf01260_w_row012=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row012_identity : leaf01260_w_row012=NestedInteger.coefficientFrom 88 12 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 12 0 leaf01260_w_affine leaf01260_w_row012 IntegerBernsteinWeights88.row012 (IntegerBernsteinTable.checked (n := 2) 88 12 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row012 leaf01260_w_affine_length IntegerBernsteinWeights88.row012_identity) leaf01260_w_row012_weighted
theorem leaf01260_w_row012_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row012=true := by decide +kernel
#print axioms leaf01260_w_row012_weighted
#print axioms leaf01260_w_row012_identity
#print axioms leaf01260_w_row012_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row013 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01260_w_affine)
theorem leaf01260_w_row013_weighted : leaf01260_w_row013=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row013_identity : leaf01260_w_row013=NestedInteger.coefficientFrom 88 13 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 13 0 leaf01260_w_affine leaf01260_w_row013 IntegerBernsteinWeights88.row013 (IntegerBernsteinTable.checked (n := 2) 88 13 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row013 leaf01260_w_affine_length IntegerBernsteinWeights88.row013_identity) leaf01260_w_row013_weighted
theorem leaf01260_w_row013_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row013=true := by decide +kernel
#print axioms leaf01260_w_row013_weighted
#print axioms leaf01260_w_row013_identity
#print axioms leaf01260_w_row013_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row014 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01260_w_affine)
theorem leaf01260_w_row014_weighted : leaf01260_w_row014=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row014_identity : leaf01260_w_row014=NestedInteger.coefficientFrom 88 14 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 14 0 leaf01260_w_affine leaf01260_w_row014 IntegerBernsteinWeights88.row014 (IntegerBernsteinTable.checked (n := 2) 88 14 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row014 leaf01260_w_affine_length IntegerBernsteinWeights88.row014_identity) leaf01260_w_row014_weighted
theorem leaf01260_w_row014_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row014=true := by decide +kernel
#print axioms leaf01260_w_row014_weighted
#print axioms leaf01260_w_row014_identity
#print axioms leaf01260_w_row014_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row015 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01260_w_affine)
theorem leaf01260_w_row015_weighted : leaf01260_w_row015=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row015_identity : leaf01260_w_row015=NestedInteger.coefficientFrom 88 15 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 15 0 leaf01260_w_affine leaf01260_w_row015 IntegerBernsteinWeights88.row015 (IntegerBernsteinTable.checked (n := 2) 88 15 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row015 leaf01260_w_affine_length IntegerBernsteinWeights88.row015_identity) leaf01260_w_row015_weighted
theorem leaf01260_w_row015_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row015=true := by decide +kernel
#print axioms leaf01260_w_row015_weighted
#print axioms leaf01260_w_row015_identity
#print axioms leaf01260_w_row015_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
