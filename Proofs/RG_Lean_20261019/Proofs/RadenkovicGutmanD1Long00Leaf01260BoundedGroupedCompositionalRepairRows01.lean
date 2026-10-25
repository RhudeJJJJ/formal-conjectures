/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairJoins02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row016 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01260_w_affine)
theorem leaf01260_w_row016_weighted : leaf01260_w_row016=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row016_identity : leaf01260_w_row016=NestedInteger.coefficientFrom 88 16 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 16 0 leaf01260_w_affine leaf01260_w_row016 IntegerBernsteinWeights88.row016 (IntegerBernsteinTable.checked (n := 2) 88 16 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row016 leaf01260_w_affine_length IntegerBernsteinWeights88.row016_identity) leaf01260_w_row016_weighted
theorem leaf01260_w_row016_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row016=true := by decide +kernel
#print axioms leaf01260_w_row016_weighted
#print axioms leaf01260_w_row016_identity
#print axioms leaf01260_w_row016_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row017 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01260_w_affine)
theorem leaf01260_w_row017_weighted : leaf01260_w_row017=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row017_identity : leaf01260_w_row017=NestedInteger.coefficientFrom 88 17 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 17 0 leaf01260_w_affine leaf01260_w_row017 IntegerBernsteinWeights88.row017 (IntegerBernsteinTable.checked (n := 2) 88 17 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row017 leaf01260_w_affine_length IntegerBernsteinWeights88.row017_identity) leaf01260_w_row017_weighted
theorem leaf01260_w_row017_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row017=true := by decide +kernel
#print axioms leaf01260_w_row017_weighted
#print axioms leaf01260_w_row017_identity
#print axioms leaf01260_w_row017_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row018 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01260_w_affine)
theorem leaf01260_w_row018_weighted : leaf01260_w_row018=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row018_identity : leaf01260_w_row018=NestedInteger.coefficientFrom 88 18 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 18 0 leaf01260_w_affine leaf01260_w_row018 IntegerBernsteinWeights88.row018 (IntegerBernsteinTable.checked (n := 2) 88 18 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row018 leaf01260_w_affine_length IntegerBernsteinWeights88.row018_identity) leaf01260_w_row018_weighted
theorem leaf01260_w_row018_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row018=true := by decide +kernel
#print axioms leaf01260_w_row018_weighted
#print axioms leaf01260_w_row018_identity
#print axioms leaf01260_w_row018_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row019 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01260_w_affine)
theorem leaf01260_w_row019_weighted : leaf01260_w_row019=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row019_identity : leaf01260_w_row019=NestedInteger.coefficientFrom 88 19 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 19 0 leaf01260_w_affine leaf01260_w_row019 IntegerBernsteinWeights88.row019 (IntegerBernsteinTable.checked (n := 2) 88 19 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row019 leaf01260_w_affine_length IntegerBernsteinWeights88.row019_identity) leaf01260_w_row019_weighted
theorem leaf01260_w_row019_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row019=true := by decide +kernel
#print axioms leaf01260_w_row019_weighted
#print axioms leaf01260_w_row019_identity
#print axioms leaf01260_w_row019_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row020 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01260_w_affine)
theorem leaf01260_w_row020_weighted : leaf01260_w_row020=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row020_identity : leaf01260_w_row020=NestedInteger.coefficientFrom 88 20 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 20 0 leaf01260_w_affine leaf01260_w_row020 IntegerBernsteinWeights88.row020 (IntegerBernsteinTable.checked (n := 2) 88 20 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row020 leaf01260_w_affine_length IntegerBernsteinWeights88.row020_identity) leaf01260_w_row020_weighted
theorem leaf01260_w_row020_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row020=true := by decide +kernel
#print axioms leaf01260_w_row020_weighted
#print axioms leaf01260_w_row020_identity
#print axioms leaf01260_w_row020_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row021 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01260_w_affine)
theorem leaf01260_w_row021_weighted : leaf01260_w_row021=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row021_identity : leaf01260_w_row021=NestedInteger.coefficientFrom 88 21 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 21 0 leaf01260_w_affine leaf01260_w_row021 IntegerBernsteinWeights88.row021 (IntegerBernsteinTable.checked (n := 2) 88 21 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row021 leaf01260_w_affine_length IntegerBernsteinWeights88.row021_identity) leaf01260_w_row021_weighted
theorem leaf01260_w_row021_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row021=true := by decide +kernel
#print axioms leaf01260_w_row021_weighted
#print axioms leaf01260_w_row021_identity
#print axioms leaf01260_w_row021_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row022 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01260_w_affine)
theorem leaf01260_w_row022_weighted : leaf01260_w_row022=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row022_identity : leaf01260_w_row022=NestedInteger.coefficientFrom 88 22 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 22 0 leaf01260_w_affine leaf01260_w_row022 IntegerBernsteinWeights88.row022 (IntegerBernsteinTable.checked (n := 2) 88 22 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row022 leaf01260_w_affine_length IntegerBernsteinWeights88.row022_identity) leaf01260_w_row022_weighted
theorem leaf01260_w_row022_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row022=true := by decide +kernel
#print axioms leaf01260_w_row022_weighted
#print axioms leaf01260_w_row022_identity
#print axioms leaf01260_w_row022_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row023 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01260_w_affine)
theorem leaf01260_w_row023_weighted : leaf01260_w_row023=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row023_identity : leaf01260_w_row023=NestedInteger.coefficientFrom 88 23 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 23 0 leaf01260_w_affine leaf01260_w_row023 IntegerBernsteinWeights88.row023 (IntegerBernsteinTable.checked (n := 2) 88 23 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row023 leaf01260_w_affine_length IntegerBernsteinWeights88.row023_identity) leaf01260_w_row023_weighted
theorem leaf01260_w_row023_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row023=true := by decide +kernel
#print axioms leaf01260_w_row023_weighted
#print axioms leaf01260_w_row023_identity
#print axioms leaf01260_w_row023_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row024 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01260_w_affine)
theorem leaf01260_w_row024_weighted : leaf01260_w_row024=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row024_identity : leaf01260_w_row024=NestedInteger.coefficientFrom 88 24 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 24 0 leaf01260_w_affine leaf01260_w_row024 IntegerBernsteinWeights88.row024 (IntegerBernsteinTable.checked (n := 2) 88 24 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row024 leaf01260_w_affine_length IntegerBernsteinWeights88.row024_identity) leaf01260_w_row024_weighted
theorem leaf01260_w_row024_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row024=true := by decide +kernel
#print axioms leaf01260_w_row024_weighted
#print axioms leaf01260_w_row024_identity
#print axioms leaf01260_w_row024_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row025 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01260_w_affine)
theorem leaf01260_w_row025_weighted : leaf01260_w_row025=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row025_identity : leaf01260_w_row025=NestedInteger.coefficientFrom 88 25 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 25 0 leaf01260_w_affine leaf01260_w_row025 IntegerBernsteinWeights88.row025 (IntegerBernsteinTable.checked (n := 2) 88 25 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row025 leaf01260_w_affine_length IntegerBernsteinWeights88.row025_identity) leaf01260_w_row025_weighted
theorem leaf01260_w_row025_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row025=true := by decide +kernel
#print axioms leaf01260_w_row025_weighted
#print axioms leaf01260_w_row025_identity
#print axioms leaf01260_w_row025_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row026 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01260_w_affine)
theorem leaf01260_w_row026_weighted : leaf01260_w_row026=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row026_identity : leaf01260_w_row026=NestedInteger.coefficientFrom 88 26 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 26 0 leaf01260_w_affine leaf01260_w_row026 IntegerBernsteinWeights88.row026 (IntegerBernsteinTable.checked (n := 2) 88 26 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row026 leaf01260_w_affine_length IntegerBernsteinWeights88.row026_identity) leaf01260_w_row026_weighted
theorem leaf01260_w_row026_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row026=true := by decide +kernel
#print axioms leaf01260_w_row026_weighted
#print axioms leaf01260_w_row026_identity
#print axioms leaf01260_w_row026_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row027 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01260_w_affine)
theorem leaf01260_w_row027_weighted : leaf01260_w_row027=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row027_identity : leaf01260_w_row027=NestedInteger.coefficientFrom 88 27 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 27 0 leaf01260_w_affine leaf01260_w_row027 IntegerBernsteinWeights88.row027 (IntegerBernsteinTable.checked (n := 2) 88 27 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row027 leaf01260_w_affine_length IntegerBernsteinWeights88.row027_identity) leaf01260_w_row027_weighted
theorem leaf01260_w_row027_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row027=true := by decide +kernel
#print axioms leaf01260_w_row027_weighted
#print axioms leaf01260_w_row027_identity
#print axioms leaf01260_w_row027_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row028 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01260_w_affine)
theorem leaf01260_w_row028_weighted : leaf01260_w_row028=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row028_identity : leaf01260_w_row028=NestedInteger.coefficientFrom 88 28 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 28 0 leaf01260_w_affine leaf01260_w_row028 IntegerBernsteinWeights88.row028 (IntegerBernsteinTable.checked (n := 2) 88 28 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row028 leaf01260_w_affine_length IntegerBernsteinWeights88.row028_identity) leaf01260_w_row028_weighted
theorem leaf01260_w_row028_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row028=true := by decide +kernel
#print axioms leaf01260_w_row028_weighted
#print axioms leaf01260_w_row028_identity
#print axioms leaf01260_w_row028_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row029 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01260_w_affine)
theorem leaf01260_w_row029_weighted : leaf01260_w_row029=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row029_identity : leaf01260_w_row029=NestedInteger.coefficientFrom 88 29 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 29 0 leaf01260_w_affine leaf01260_w_row029 IntegerBernsteinWeights88.row029 (IntegerBernsteinTable.checked (n := 2) 88 29 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row029 leaf01260_w_affine_length IntegerBernsteinWeights88.row029_identity) leaf01260_w_row029_weighted
theorem leaf01260_w_row029_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row029=true := by decide +kernel
#print axioms leaf01260_w_row029_weighted
#print axioms leaf01260_w_row029_identity
#print axioms leaf01260_w_row029_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row030 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01260_w_affine)
theorem leaf01260_w_row030_weighted : leaf01260_w_row030=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row030_identity : leaf01260_w_row030=NestedInteger.coefficientFrom 88 30 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 30 0 leaf01260_w_affine leaf01260_w_row030 IntegerBernsteinWeights88.row030 (IntegerBernsteinTable.checked (n := 2) 88 30 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row030 leaf01260_w_affine_length IntegerBernsteinWeights88.row030_identity) leaf01260_w_row030_weighted
theorem leaf01260_w_row030_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row030=true := by decide +kernel
#print axioms leaf01260_w_row030_weighted
#print axioms leaf01260_w_row030_identity
#print axioms leaf01260_w_row030_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row031 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01260_w_affine)
theorem leaf01260_w_row031_weighted : leaf01260_w_row031=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row031_identity : leaf01260_w_row031=NestedInteger.coefficientFrom 88 31 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 31 0 leaf01260_w_affine leaf01260_w_row031 IntegerBernsteinWeights88.row031 (IntegerBernsteinTable.checked (n := 2) 88 31 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row031 leaf01260_w_affine_length IntegerBernsteinWeights88.row031_identity) leaf01260_w_row031_weighted
theorem leaf01260_w_row031_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row031=true := by decide +kernel
#print axioms leaf01260_w_row031_weighted
#print axioms leaf01260_w_row031_identity
#print axioms leaf01260_w_row031_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
