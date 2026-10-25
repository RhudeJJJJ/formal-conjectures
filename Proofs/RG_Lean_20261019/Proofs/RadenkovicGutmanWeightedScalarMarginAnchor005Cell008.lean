/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPreparedAffineAnchor005Cell008
import Proofs.RadenkovicGutmanIntegerBernsteinScalarRows
import Proofs.RadenkovicGutmanIntegerBernsteinWeights117
namespace Gebendorfer.RadenkovicGutman.WeightedScalarMarginAnchor005Cell008
open PreparedAffineAnchor005Cell008
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem length_checked : preparedMargin.length=117 := by decide +kernel
#print axioms length_checked
noncomputable def row000 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row000 preparedMargin]]).head!.head!
theorem row000_weighted : row000=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row000 preparedMargin := by decide +kernel
#print axioms row000_weighted
theorem row000_identity : row000=NestedInteger.coefficientFrom (n := 0) 117 0 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 0 0 preparedMargin row000 IntegerBernsteinWeights117.row000
    (IntegerBernsteinTable.checked (n := 0) 117 0 0 117 preparedMargin IntegerBernsteinWeights117.row000 length_checked IntegerBernsteinWeights117.row000_identity) row000_weighted
#print axioms row000_identity
theorem row000_nonnegative : 0≤row000 := by decide +kernel
#print axioms row000_nonnegative
noncomputable def row001 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row001 preparedMargin]]).head!.head!
theorem row001_weighted : row001=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row001 preparedMargin := by decide +kernel
#print axioms row001_weighted
theorem row001_identity : row001=NestedInteger.coefficientFrom (n := 0) 117 1 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 1 0 preparedMargin row001 IntegerBernsteinWeights117.row001
    (IntegerBernsteinTable.checked (n := 0) 117 1 0 117 preparedMargin IntegerBernsteinWeights117.row001 length_checked IntegerBernsteinWeights117.row001_identity) row001_weighted
#print axioms row001_identity
theorem row001_nonnegative : 0≤row001 := by decide +kernel
#print axioms row001_nonnegative
noncomputable def row002 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row002 preparedMargin]]).head!.head!
theorem row002_weighted : row002=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row002 preparedMargin := by decide +kernel
#print axioms row002_weighted
theorem row002_identity : row002=NestedInteger.coefficientFrom (n := 0) 117 2 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 2 0 preparedMargin row002 IntegerBernsteinWeights117.row002
    (IntegerBernsteinTable.checked (n := 0) 117 2 0 117 preparedMargin IntegerBernsteinWeights117.row002 length_checked IntegerBernsteinWeights117.row002_identity) row002_weighted
#print axioms row002_identity
theorem row002_nonnegative : 0≤row002 := by decide +kernel
#print axioms row002_nonnegative
noncomputable def row003 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row003 preparedMargin]]).head!.head!
theorem row003_weighted : row003=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row003 preparedMargin := by decide +kernel
#print axioms row003_weighted
theorem row003_identity : row003=NestedInteger.coefficientFrom (n := 0) 117 3 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 3 0 preparedMargin row003 IntegerBernsteinWeights117.row003
    (IntegerBernsteinTable.checked (n := 0) 117 3 0 117 preparedMargin IntegerBernsteinWeights117.row003 length_checked IntegerBernsteinWeights117.row003_identity) row003_weighted
#print axioms row003_identity
theorem row003_nonnegative : 0≤row003 := by decide +kernel
#print axioms row003_nonnegative
noncomputable def row004 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row004 preparedMargin]]).head!.head!
theorem row004_weighted : row004=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row004 preparedMargin := by decide +kernel
#print axioms row004_weighted
theorem row004_identity : row004=NestedInteger.coefficientFrom (n := 0) 117 4 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 4 0 preparedMargin row004 IntegerBernsteinWeights117.row004
    (IntegerBernsteinTable.checked (n := 0) 117 4 0 117 preparedMargin IntegerBernsteinWeights117.row004 length_checked IntegerBernsteinWeights117.row004_identity) row004_weighted
#print axioms row004_identity
theorem row004_nonnegative : 0≤row004 := by decide +kernel
#print axioms row004_nonnegative
noncomputable def row005 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row005 preparedMargin]]).head!.head!
theorem row005_weighted : row005=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row005 preparedMargin := by decide +kernel
#print axioms row005_weighted
theorem row005_identity : row005=NestedInteger.coefficientFrom (n := 0) 117 5 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 5 0 preparedMargin row005 IntegerBernsteinWeights117.row005
    (IntegerBernsteinTable.checked (n := 0) 117 5 0 117 preparedMargin IntegerBernsteinWeights117.row005 length_checked IntegerBernsteinWeights117.row005_identity) row005_weighted
#print axioms row005_identity
theorem row005_nonnegative : 0≤row005 := by decide +kernel
#print axioms row005_nonnegative
noncomputable def row006 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row006 preparedMargin]]).head!.head!
theorem row006_weighted : row006=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row006 preparedMargin := by decide +kernel
#print axioms row006_weighted
theorem row006_identity : row006=NestedInteger.coefficientFrom (n := 0) 117 6 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 6 0 preparedMargin row006 IntegerBernsteinWeights117.row006
    (IntegerBernsteinTable.checked (n := 0) 117 6 0 117 preparedMargin IntegerBernsteinWeights117.row006 length_checked IntegerBernsteinWeights117.row006_identity) row006_weighted
#print axioms row006_identity
theorem row006_nonnegative : 0≤row006 := by decide +kernel
#print axioms row006_nonnegative
noncomputable def row007 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row007 preparedMargin]]).head!.head!
theorem row007_weighted : row007=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row007 preparedMargin := by decide +kernel
#print axioms row007_weighted
theorem row007_identity : row007=NestedInteger.coefficientFrom (n := 0) 117 7 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 7 0 preparedMargin row007 IntegerBernsteinWeights117.row007
    (IntegerBernsteinTable.checked (n := 0) 117 7 0 117 preparedMargin IntegerBernsteinWeights117.row007 length_checked IntegerBernsteinWeights117.row007_identity) row007_weighted
#print axioms row007_identity
theorem row007_nonnegative : 0≤row007 := by decide +kernel
#print axioms row007_nonnegative
noncomputable def row008 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row008 preparedMargin]]).head!.head!
theorem row008_weighted : row008=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row008 preparedMargin := by decide +kernel
#print axioms row008_weighted
theorem row008_identity : row008=NestedInteger.coefficientFrom (n := 0) 117 8 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 8 0 preparedMargin row008 IntegerBernsteinWeights117.row008
    (IntegerBernsteinTable.checked (n := 0) 117 8 0 117 preparedMargin IntegerBernsteinWeights117.row008 length_checked IntegerBernsteinWeights117.row008_identity) row008_weighted
#print axioms row008_identity
theorem row008_nonnegative : 0≤row008 := by decide +kernel
#print axioms row008_nonnegative
noncomputable def row009 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row009 preparedMargin]]).head!.head!
theorem row009_weighted : row009=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row009 preparedMargin := by decide +kernel
#print axioms row009_weighted
theorem row009_identity : row009=NestedInteger.coefficientFrom (n := 0) 117 9 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 9 0 preparedMargin row009 IntegerBernsteinWeights117.row009
    (IntegerBernsteinTable.checked (n := 0) 117 9 0 117 preparedMargin IntegerBernsteinWeights117.row009 length_checked IntegerBernsteinWeights117.row009_identity) row009_weighted
#print axioms row009_identity
theorem row009_nonnegative : 0≤row009 := by decide +kernel
#print axioms row009_nonnegative
noncomputable def row010 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row010 preparedMargin]]).head!.head!
theorem row010_weighted : row010=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row010 preparedMargin := by decide +kernel
#print axioms row010_weighted
theorem row010_identity : row010=NestedInteger.coefficientFrom (n := 0) 117 10 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 10 0 preparedMargin row010 IntegerBernsteinWeights117.row010
    (IntegerBernsteinTable.checked (n := 0) 117 10 0 117 preparedMargin IntegerBernsteinWeights117.row010 length_checked IntegerBernsteinWeights117.row010_identity) row010_weighted
#print axioms row010_identity
theorem row010_nonnegative : 0≤row010 := by decide +kernel
#print axioms row010_nonnegative
noncomputable def row011 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row011 preparedMargin]]).head!.head!
theorem row011_weighted : row011=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row011 preparedMargin := by decide +kernel
#print axioms row011_weighted
theorem row011_identity : row011=NestedInteger.coefficientFrom (n := 0) 117 11 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 11 0 preparedMargin row011 IntegerBernsteinWeights117.row011
    (IntegerBernsteinTable.checked (n := 0) 117 11 0 117 preparedMargin IntegerBernsteinWeights117.row011 length_checked IntegerBernsteinWeights117.row011_identity) row011_weighted
#print axioms row011_identity
theorem row011_nonnegative : 0≤row011 := by decide +kernel
#print axioms row011_nonnegative
noncomputable def row012 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row012 preparedMargin]]).head!.head!
theorem row012_weighted : row012=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row012 preparedMargin := by decide +kernel
#print axioms row012_weighted
theorem row012_identity : row012=NestedInteger.coefficientFrom (n := 0) 117 12 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 12 0 preparedMargin row012 IntegerBernsteinWeights117.row012
    (IntegerBernsteinTable.checked (n := 0) 117 12 0 117 preparedMargin IntegerBernsteinWeights117.row012 length_checked IntegerBernsteinWeights117.row012_identity) row012_weighted
#print axioms row012_identity
theorem row012_nonnegative : 0≤row012 := by decide +kernel
#print axioms row012_nonnegative
noncomputable def row013 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row013 preparedMargin]]).head!.head!
theorem row013_weighted : row013=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row013 preparedMargin := by decide +kernel
#print axioms row013_weighted
theorem row013_identity : row013=NestedInteger.coefficientFrom (n := 0) 117 13 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 13 0 preparedMargin row013 IntegerBernsteinWeights117.row013
    (IntegerBernsteinTable.checked (n := 0) 117 13 0 117 preparedMargin IntegerBernsteinWeights117.row013 length_checked IntegerBernsteinWeights117.row013_identity) row013_weighted
#print axioms row013_identity
theorem row013_nonnegative : 0≤row013 := by decide +kernel
#print axioms row013_nonnegative
noncomputable def row014 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row014 preparedMargin]]).head!.head!
theorem row014_weighted : row014=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row014 preparedMargin := by decide +kernel
#print axioms row014_weighted
theorem row014_identity : row014=NestedInteger.coefficientFrom (n := 0) 117 14 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 14 0 preparedMargin row014 IntegerBernsteinWeights117.row014
    (IntegerBernsteinTable.checked (n := 0) 117 14 0 117 preparedMargin IntegerBernsteinWeights117.row014 length_checked IntegerBernsteinWeights117.row014_identity) row014_weighted
#print axioms row014_identity
theorem row014_nonnegative : 0≤row014 := by decide +kernel
#print axioms row014_nonnegative
noncomputable def row015 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row015 preparedMargin]]).head!.head!
theorem row015_weighted : row015=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row015 preparedMargin := by decide +kernel
#print axioms row015_weighted
theorem row015_identity : row015=NestedInteger.coefficientFrom (n := 0) 117 15 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 15 0 preparedMargin row015 IntegerBernsteinWeights117.row015
    (IntegerBernsteinTable.checked (n := 0) 117 15 0 117 preparedMargin IntegerBernsteinWeights117.row015 length_checked IntegerBernsteinWeights117.row015_identity) row015_weighted
#print axioms row015_identity
theorem row015_nonnegative : 0≤row015 := by decide +kernel
#print axioms row015_nonnegative
noncomputable def row016 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row016 preparedMargin]]).head!.head!
theorem row016_weighted : row016=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row016 preparedMargin := by decide +kernel
#print axioms row016_weighted
theorem row016_identity : row016=NestedInteger.coefficientFrom (n := 0) 117 16 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 16 0 preparedMargin row016 IntegerBernsteinWeights117.row016
    (IntegerBernsteinTable.checked (n := 0) 117 16 0 117 preparedMargin IntegerBernsteinWeights117.row016 length_checked IntegerBernsteinWeights117.row016_identity) row016_weighted
#print axioms row016_identity
theorem row016_nonnegative : 0≤row016 := by decide +kernel
#print axioms row016_nonnegative
noncomputable def row017 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row017 preparedMargin]]).head!.head!
theorem row017_weighted : row017=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row017 preparedMargin := by decide +kernel
#print axioms row017_weighted
theorem row017_identity : row017=NestedInteger.coefficientFrom (n := 0) 117 17 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 17 0 preparedMargin row017 IntegerBernsteinWeights117.row017
    (IntegerBernsteinTable.checked (n := 0) 117 17 0 117 preparedMargin IntegerBernsteinWeights117.row017 length_checked IntegerBernsteinWeights117.row017_identity) row017_weighted
#print axioms row017_identity
theorem row017_nonnegative : 0≤row017 := by decide +kernel
#print axioms row017_nonnegative
noncomputable def row018 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row018 preparedMargin]]).head!.head!
theorem row018_weighted : row018=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row018 preparedMargin := by decide +kernel
#print axioms row018_weighted
theorem row018_identity : row018=NestedInteger.coefficientFrom (n := 0) 117 18 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 18 0 preparedMargin row018 IntegerBernsteinWeights117.row018
    (IntegerBernsteinTable.checked (n := 0) 117 18 0 117 preparedMargin IntegerBernsteinWeights117.row018 length_checked IntegerBernsteinWeights117.row018_identity) row018_weighted
#print axioms row018_identity
theorem row018_nonnegative : 0≤row018 := by decide +kernel
#print axioms row018_nonnegative
noncomputable def row019 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row019 preparedMargin]]).head!.head!
theorem row019_weighted : row019=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row019 preparedMargin := by decide +kernel
#print axioms row019_weighted
theorem row019_identity : row019=NestedInteger.coefficientFrom (n := 0) 117 19 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 19 0 preparedMargin row019 IntegerBernsteinWeights117.row019
    (IntegerBernsteinTable.checked (n := 0) 117 19 0 117 preparedMargin IntegerBernsteinWeights117.row019 length_checked IntegerBernsteinWeights117.row019_identity) row019_weighted
#print axioms row019_identity
theorem row019_nonnegative : 0≤row019 := by decide +kernel
#print axioms row019_nonnegative
noncomputable def row020 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row020 preparedMargin]]).head!.head!
theorem row020_weighted : row020=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row020 preparedMargin := by decide +kernel
#print axioms row020_weighted
theorem row020_identity : row020=NestedInteger.coefficientFrom (n := 0) 117 20 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 20 0 preparedMargin row020 IntegerBernsteinWeights117.row020
    (IntegerBernsteinTable.checked (n := 0) 117 20 0 117 preparedMargin IntegerBernsteinWeights117.row020 length_checked IntegerBernsteinWeights117.row020_identity) row020_weighted
#print axioms row020_identity
theorem row020_nonnegative : 0≤row020 := by decide +kernel
#print axioms row020_nonnegative
noncomputable def row021 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row021 preparedMargin]]).head!.head!
theorem row021_weighted : row021=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row021 preparedMargin := by decide +kernel
#print axioms row021_weighted
theorem row021_identity : row021=NestedInteger.coefficientFrom (n := 0) 117 21 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 21 0 preparedMargin row021 IntegerBernsteinWeights117.row021
    (IntegerBernsteinTable.checked (n := 0) 117 21 0 117 preparedMargin IntegerBernsteinWeights117.row021 length_checked IntegerBernsteinWeights117.row021_identity) row021_weighted
#print axioms row021_identity
theorem row021_nonnegative : 0≤row021 := by decide +kernel
#print axioms row021_nonnegative
noncomputable def row022 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row022 preparedMargin]]).head!.head!
theorem row022_weighted : row022=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row022 preparedMargin := by decide +kernel
#print axioms row022_weighted
theorem row022_identity : row022=NestedInteger.coefficientFrom (n := 0) 117 22 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 22 0 preparedMargin row022 IntegerBernsteinWeights117.row022
    (IntegerBernsteinTable.checked (n := 0) 117 22 0 117 preparedMargin IntegerBernsteinWeights117.row022 length_checked IntegerBernsteinWeights117.row022_identity) row022_weighted
#print axioms row022_identity
theorem row022_nonnegative : 0≤row022 := by decide +kernel
#print axioms row022_nonnegative
noncomputable def row023 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row023 preparedMargin]]).head!.head!
theorem row023_weighted : row023=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row023 preparedMargin := by decide +kernel
#print axioms row023_weighted
theorem row023_identity : row023=NestedInteger.coefficientFrom (n := 0) 117 23 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 23 0 preparedMargin row023 IntegerBernsteinWeights117.row023
    (IntegerBernsteinTable.checked (n := 0) 117 23 0 117 preparedMargin IntegerBernsteinWeights117.row023 length_checked IntegerBernsteinWeights117.row023_identity) row023_weighted
#print axioms row023_identity
theorem row023_nonnegative : 0≤row023 := by decide +kernel
#print axioms row023_nonnegative
noncomputable def row024 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row024 preparedMargin]]).head!.head!
theorem row024_weighted : row024=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row024 preparedMargin := by decide +kernel
#print axioms row024_weighted
theorem row024_identity : row024=NestedInteger.coefficientFrom (n := 0) 117 24 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 24 0 preparedMargin row024 IntegerBernsteinWeights117.row024
    (IntegerBernsteinTable.checked (n := 0) 117 24 0 117 preparedMargin IntegerBernsteinWeights117.row024 length_checked IntegerBernsteinWeights117.row024_identity) row024_weighted
#print axioms row024_identity
theorem row024_nonnegative : 0≤row024 := by decide +kernel
#print axioms row024_nonnegative
noncomputable def row025 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row025 preparedMargin]]).head!.head!
theorem row025_weighted : row025=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row025 preparedMargin := by decide +kernel
#print axioms row025_weighted
theorem row025_identity : row025=NestedInteger.coefficientFrom (n := 0) 117 25 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 25 0 preparedMargin row025 IntegerBernsteinWeights117.row025
    (IntegerBernsteinTable.checked (n := 0) 117 25 0 117 preparedMargin IntegerBernsteinWeights117.row025 length_checked IntegerBernsteinWeights117.row025_identity) row025_weighted
#print axioms row025_identity
theorem row025_nonnegative : 0≤row025 := by decide +kernel
#print axioms row025_nonnegative
noncomputable def row026 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row026 preparedMargin]]).head!.head!
theorem row026_weighted : row026=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row026 preparedMargin := by decide +kernel
#print axioms row026_weighted
theorem row026_identity : row026=NestedInteger.coefficientFrom (n := 0) 117 26 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 26 0 preparedMargin row026 IntegerBernsteinWeights117.row026
    (IntegerBernsteinTable.checked (n := 0) 117 26 0 117 preparedMargin IntegerBernsteinWeights117.row026 length_checked IntegerBernsteinWeights117.row026_identity) row026_weighted
#print axioms row026_identity
theorem row026_nonnegative : 0≤row026 := by decide +kernel
#print axioms row026_nonnegative
noncomputable def row027 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row027 preparedMargin]]).head!.head!
theorem row027_weighted : row027=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row027 preparedMargin := by decide +kernel
#print axioms row027_weighted
theorem row027_identity : row027=NestedInteger.coefficientFrom (n := 0) 117 27 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 27 0 preparedMargin row027 IntegerBernsteinWeights117.row027
    (IntegerBernsteinTable.checked (n := 0) 117 27 0 117 preparedMargin IntegerBernsteinWeights117.row027 length_checked IntegerBernsteinWeights117.row027_identity) row027_weighted
#print axioms row027_identity
theorem row027_nonnegative : 0≤row027 := by decide +kernel
#print axioms row027_nonnegative
noncomputable def row028 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row028 preparedMargin]]).head!.head!
theorem row028_weighted : row028=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row028 preparedMargin := by decide +kernel
#print axioms row028_weighted
theorem row028_identity : row028=NestedInteger.coefficientFrom (n := 0) 117 28 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 28 0 preparedMargin row028 IntegerBernsteinWeights117.row028
    (IntegerBernsteinTable.checked (n := 0) 117 28 0 117 preparedMargin IntegerBernsteinWeights117.row028 length_checked IntegerBernsteinWeights117.row028_identity) row028_weighted
#print axioms row028_identity
theorem row028_nonnegative : 0≤row028 := by decide +kernel
#print axioms row028_nonnegative
noncomputable def row029 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row029 preparedMargin]]).head!.head!
theorem row029_weighted : row029=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row029 preparedMargin := by decide +kernel
#print axioms row029_weighted
theorem row029_identity : row029=NestedInteger.coefficientFrom (n := 0) 117 29 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 29 0 preparedMargin row029 IntegerBernsteinWeights117.row029
    (IntegerBernsteinTable.checked (n := 0) 117 29 0 117 preparedMargin IntegerBernsteinWeights117.row029 length_checked IntegerBernsteinWeights117.row029_identity) row029_weighted
#print axioms row029_identity
theorem row029_nonnegative : 0≤row029 := by decide +kernel
#print axioms row029_nonnegative
noncomputable def row030 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row030 preparedMargin]]).head!.head!
theorem row030_weighted : row030=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row030 preparedMargin := by decide +kernel
#print axioms row030_weighted
theorem row030_identity : row030=NestedInteger.coefficientFrom (n := 0) 117 30 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 30 0 preparedMargin row030 IntegerBernsteinWeights117.row030
    (IntegerBernsteinTable.checked (n := 0) 117 30 0 117 preparedMargin IntegerBernsteinWeights117.row030 length_checked IntegerBernsteinWeights117.row030_identity) row030_weighted
#print axioms row030_identity
theorem row030_nonnegative : 0≤row030 := by decide +kernel
#print axioms row030_nonnegative
noncomputable def row031 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row031 preparedMargin]]).head!.head!
theorem row031_weighted : row031=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row031 preparedMargin := by decide +kernel
#print axioms row031_weighted
theorem row031_identity : row031=NestedInteger.coefficientFrom (n := 0) 117 31 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 31 0 preparedMargin row031 IntegerBernsteinWeights117.row031
    (IntegerBernsteinTable.checked (n := 0) 117 31 0 117 preparedMargin IntegerBernsteinWeights117.row031 length_checked IntegerBernsteinWeights117.row031_identity) row031_weighted
#print axioms row031_identity
theorem row031_nonnegative : 0≤row031 := by decide +kernel
#print axioms row031_nonnegative
noncomputable def row032 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row032 preparedMargin]]).head!.head!
theorem row032_weighted : row032=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row032 preparedMargin := by decide +kernel
#print axioms row032_weighted
theorem row032_identity : row032=NestedInteger.coefficientFrom (n := 0) 117 32 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 32 0 preparedMargin row032 IntegerBernsteinWeights117.row032
    (IntegerBernsteinTable.checked (n := 0) 117 32 0 117 preparedMargin IntegerBernsteinWeights117.row032 length_checked IntegerBernsteinWeights117.row032_identity) row032_weighted
#print axioms row032_identity
theorem row032_nonnegative : 0≤row032 := by decide +kernel
#print axioms row032_nonnegative
noncomputable def row033 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row033 preparedMargin]]).head!.head!
theorem row033_weighted : row033=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row033 preparedMargin := by decide +kernel
#print axioms row033_weighted
theorem row033_identity : row033=NestedInteger.coefficientFrom (n := 0) 117 33 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 33 0 preparedMargin row033 IntegerBernsteinWeights117.row033
    (IntegerBernsteinTable.checked (n := 0) 117 33 0 117 preparedMargin IntegerBernsteinWeights117.row033 length_checked IntegerBernsteinWeights117.row033_identity) row033_weighted
#print axioms row033_identity
theorem row033_nonnegative : 0≤row033 := by decide +kernel
#print axioms row033_nonnegative
noncomputable def row034 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row034 preparedMargin]]).head!.head!
theorem row034_weighted : row034=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row034 preparedMargin := by decide +kernel
#print axioms row034_weighted
theorem row034_identity : row034=NestedInteger.coefficientFrom (n := 0) 117 34 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 34 0 preparedMargin row034 IntegerBernsteinWeights117.row034
    (IntegerBernsteinTable.checked (n := 0) 117 34 0 117 preparedMargin IntegerBernsteinWeights117.row034 length_checked IntegerBernsteinWeights117.row034_identity) row034_weighted
#print axioms row034_identity
theorem row034_nonnegative : 0≤row034 := by decide +kernel
#print axioms row034_nonnegative
noncomputable def row035 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row035 preparedMargin]]).head!.head!
theorem row035_weighted : row035=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row035 preparedMargin := by decide +kernel
#print axioms row035_weighted
theorem row035_identity : row035=NestedInteger.coefficientFrom (n := 0) 117 35 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 35 0 preparedMargin row035 IntegerBernsteinWeights117.row035
    (IntegerBernsteinTable.checked (n := 0) 117 35 0 117 preparedMargin IntegerBernsteinWeights117.row035 length_checked IntegerBernsteinWeights117.row035_identity) row035_weighted
#print axioms row035_identity
theorem row035_nonnegative : 0≤row035 := by decide +kernel
#print axioms row035_nonnegative
noncomputable def row036 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row036 preparedMargin]]).head!.head!
theorem row036_weighted : row036=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row036 preparedMargin := by decide +kernel
#print axioms row036_weighted
theorem row036_identity : row036=NestedInteger.coefficientFrom (n := 0) 117 36 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 36 0 preparedMargin row036 IntegerBernsteinWeights117.row036
    (IntegerBernsteinTable.checked (n := 0) 117 36 0 117 preparedMargin IntegerBernsteinWeights117.row036 length_checked IntegerBernsteinWeights117.row036_identity) row036_weighted
#print axioms row036_identity
theorem row036_nonnegative : 0≤row036 := by decide +kernel
#print axioms row036_nonnegative
noncomputable def row037 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row037 preparedMargin]]).head!.head!
theorem row037_weighted : row037=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row037 preparedMargin := by decide +kernel
#print axioms row037_weighted
theorem row037_identity : row037=NestedInteger.coefficientFrom (n := 0) 117 37 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 37 0 preparedMargin row037 IntegerBernsteinWeights117.row037
    (IntegerBernsteinTable.checked (n := 0) 117 37 0 117 preparedMargin IntegerBernsteinWeights117.row037 length_checked IntegerBernsteinWeights117.row037_identity) row037_weighted
#print axioms row037_identity
theorem row037_nonnegative : 0≤row037 := by decide +kernel
#print axioms row037_nonnegative
noncomputable def row038 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row038 preparedMargin]]).head!.head!
theorem row038_weighted : row038=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row038 preparedMargin := by decide +kernel
#print axioms row038_weighted
theorem row038_identity : row038=NestedInteger.coefficientFrom (n := 0) 117 38 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 38 0 preparedMargin row038 IntegerBernsteinWeights117.row038
    (IntegerBernsteinTable.checked (n := 0) 117 38 0 117 preparedMargin IntegerBernsteinWeights117.row038 length_checked IntegerBernsteinWeights117.row038_identity) row038_weighted
#print axioms row038_identity
theorem row038_nonnegative : 0≤row038 := by decide +kernel
#print axioms row038_nonnegative
noncomputable def row039 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row039 preparedMargin]]).head!.head!
theorem row039_weighted : row039=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row039 preparedMargin := by decide +kernel
#print axioms row039_weighted
theorem row039_identity : row039=NestedInteger.coefficientFrom (n := 0) 117 39 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 39 0 preparedMargin row039 IntegerBernsteinWeights117.row039
    (IntegerBernsteinTable.checked (n := 0) 117 39 0 117 preparedMargin IntegerBernsteinWeights117.row039 length_checked IntegerBernsteinWeights117.row039_identity) row039_weighted
#print axioms row039_identity
theorem row039_nonnegative : 0≤row039 := by decide +kernel
#print axioms row039_nonnegative
noncomputable def row040 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row040 preparedMargin]]).head!.head!
theorem row040_weighted : row040=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row040 preparedMargin := by decide +kernel
#print axioms row040_weighted
theorem row040_identity : row040=NestedInteger.coefficientFrom (n := 0) 117 40 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 40 0 preparedMargin row040 IntegerBernsteinWeights117.row040
    (IntegerBernsteinTable.checked (n := 0) 117 40 0 117 preparedMargin IntegerBernsteinWeights117.row040 length_checked IntegerBernsteinWeights117.row040_identity) row040_weighted
#print axioms row040_identity
theorem row040_nonnegative : 0≤row040 := by decide +kernel
#print axioms row040_nonnegative
noncomputable def row041 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row041 preparedMargin]]).head!.head!
theorem row041_weighted : row041=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row041 preparedMargin := by decide +kernel
#print axioms row041_weighted
theorem row041_identity : row041=NestedInteger.coefficientFrom (n := 0) 117 41 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 41 0 preparedMargin row041 IntegerBernsteinWeights117.row041
    (IntegerBernsteinTable.checked (n := 0) 117 41 0 117 preparedMargin IntegerBernsteinWeights117.row041 length_checked IntegerBernsteinWeights117.row041_identity) row041_weighted
#print axioms row041_identity
theorem row041_nonnegative : 0≤row041 := by decide +kernel
#print axioms row041_nonnegative
noncomputable def row042 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row042 preparedMargin]]).head!.head!
theorem row042_weighted : row042=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row042 preparedMargin := by decide +kernel
#print axioms row042_weighted
theorem row042_identity : row042=NestedInteger.coefficientFrom (n := 0) 117 42 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 42 0 preparedMargin row042 IntegerBernsteinWeights117.row042
    (IntegerBernsteinTable.checked (n := 0) 117 42 0 117 preparedMargin IntegerBernsteinWeights117.row042 length_checked IntegerBernsteinWeights117.row042_identity) row042_weighted
#print axioms row042_identity
theorem row042_nonnegative : 0≤row042 := by decide +kernel
#print axioms row042_nonnegative
noncomputable def row043 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row043 preparedMargin]]).head!.head!
theorem row043_weighted : row043=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row043 preparedMargin := by decide +kernel
#print axioms row043_weighted
theorem row043_identity : row043=NestedInteger.coefficientFrom (n := 0) 117 43 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 43 0 preparedMargin row043 IntegerBernsteinWeights117.row043
    (IntegerBernsteinTable.checked (n := 0) 117 43 0 117 preparedMargin IntegerBernsteinWeights117.row043 length_checked IntegerBernsteinWeights117.row043_identity) row043_weighted
#print axioms row043_identity
theorem row043_nonnegative : 0≤row043 := by decide +kernel
#print axioms row043_nonnegative
noncomputable def row044 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row044 preparedMargin]]).head!.head!
theorem row044_weighted : row044=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row044 preparedMargin := by decide +kernel
#print axioms row044_weighted
theorem row044_identity : row044=NestedInteger.coefficientFrom (n := 0) 117 44 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 44 0 preparedMargin row044 IntegerBernsteinWeights117.row044
    (IntegerBernsteinTable.checked (n := 0) 117 44 0 117 preparedMargin IntegerBernsteinWeights117.row044 length_checked IntegerBernsteinWeights117.row044_identity) row044_weighted
#print axioms row044_identity
theorem row044_nonnegative : 0≤row044 := by decide +kernel
#print axioms row044_nonnegative
noncomputable def row045 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row045 preparedMargin]]).head!.head!
theorem row045_weighted : row045=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row045 preparedMargin := by decide +kernel
#print axioms row045_weighted
theorem row045_identity : row045=NestedInteger.coefficientFrom (n := 0) 117 45 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 45 0 preparedMargin row045 IntegerBernsteinWeights117.row045
    (IntegerBernsteinTable.checked (n := 0) 117 45 0 117 preparedMargin IntegerBernsteinWeights117.row045 length_checked IntegerBernsteinWeights117.row045_identity) row045_weighted
#print axioms row045_identity
theorem row045_nonnegative : 0≤row045 := by decide +kernel
#print axioms row045_nonnegative
noncomputable def row046 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row046 preparedMargin]]).head!.head!
theorem row046_weighted : row046=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row046 preparedMargin := by decide +kernel
#print axioms row046_weighted
theorem row046_identity : row046=NestedInteger.coefficientFrom (n := 0) 117 46 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 46 0 preparedMargin row046 IntegerBernsteinWeights117.row046
    (IntegerBernsteinTable.checked (n := 0) 117 46 0 117 preparedMargin IntegerBernsteinWeights117.row046 length_checked IntegerBernsteinWeights117.row046_identity) row046_weighted
#print axioms row046_identity
theorem row046_nonnegative : 0≤row046 := by decide +kernel
#print axioms row046_nonnegative
noncomputable def row047 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row047 preparedMargin]]).head!.head!
theorem row047_weighted : row047=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row047 preparedMargin := by decide +kernel
#print axioms row047_weighted
theorem row047_identity : row047=NestedInteger.coefficientFrom (n := 0) 117 47 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 47 0 preparedMargin row047 IntegerBernsteinWeights117.row047
    (IntegerBernsteinTable.checked (n := 0) 117 47 0 117 preparedMargin IntegerBernsteinWeights117.row047 length_checked IntegerBernsteinWeights117.row047_identity) row047_weighted
#print axioms row047_identity
theorem row047_nonnegative : 0≤row047 := by decide +kernel
#print axioms row047_nonnegative
noncomputable def row048 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row048 preparedMargin]]).head!.head!
theorem row048_weighted : row048=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row048 preparedMargin := by decide +kernel
#print axioms row048_weighted
theorem row048_identity : row048=NestedInteger.coefficientFrom (n := 0) 117 48 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 48 0 preparedMargin row048 IntegerBernsteinWeights117.row048
    (IntegerBernsteinTable.checked (n := 0) 117 48 0 117 preparedMargin IntegerBernsteinWeights117.row048 length_checked IntegerBernsteinWeights117.row048_identity) row048_weighted
#print axioms row048_identity
theorem row048_nonnegative : 0≤row048 := by decide +kernel
#print axioms row048_nonnegative
noncomputable def row049 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row049 preparedMargin]]).head!.head!
theorem row049_weighted : row049=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row049 preparedMargin := by decide +kernel
#print axioms row049_weighted
theorem row049_identity : row049=NestedInteger.coefficientFrom (n := 0) 117 49 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 49 0 preparedMargin row049 IntegerBernsteinWeights117.row049
    (IntegerBernsteinTable.checked (n := 0) 117 49 0 117 preparedMargin IntegerBernsteinWeights117.row049 length_checked IntegerBernsteinWeights117.row049_identity) row049_weighted
#print axioms row049_identity
theorem row049_nonnegative : 0≤row049 := by decide +kernel
#print axioms row049_nonnegative
noncomputable def row050 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row050 preparedMargin]]).head!.head!
theorem row050_weighted : row050=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row050 preparedMargin := by decide +kernel
#print axioms row050_weighted
theorem row050_identity : row050=NestedInteger.coefficientFrom (n := 0) 117 50 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 50 0 preparedMargin row050 IntegerBernsteinWeights117.row050
    (IntegerBernsteinTable.checked (n := 0) 117 50 0 117 preparedMargin IntegerBernsteinWeights117.row050 length_checked IntegerBernsteinWeights117.row050_identity) row050_weighted
#print axioms row050_identity
theorem row050_nonnegative : 0≤row050 := by decide +kernel
#print axioms row050_nonnegative
noncomputable def row051 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row051 preparedMargin]]).head!.head!
theorem row051_weighted : row051=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row051 preparedMargin := by decide +kernel
#print axioms row051_weighted
theorem row051_identity : row051=NestedInteger.coefficientFrom (n := 0) 117 51 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 51 0 preparedMargin row051 IntegerBernsteinWeights117.row051
    (IntegerBernsteinTable.checked (n := 0) 117 51 0 117 preparedMargin IntegerBernsteinWeights117.row051 length_checked IntegerBernsteinWeights117.row051_identity) row051_weighted
#print axioms row051_identity
theorem row051_nonnegative : 0≤row051 := by decide +kernel
#print axioms row051_nonnegative
noncomputable def row052 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row052 preparedMargin]]).head!.head!
theorem row052_weighted : row052=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row052 preparedMargin := by decide +kernel
#print axioms row052_weighted
theorem row052_identity : row052=NestedInteger.coefficientFrom (n := 0) 117 52 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 52 0 preparedMargin row052 IntegerBernsteinWeights117.row052
    (IntegerBernsteinTable.checked (n := 0) 117 52 0 117 preparedMargin IntegerBernsteinWeights117.row052 length_checked IntegerBernsteinWeights117.row052_identity) row052_weighted
#print axioms row052_identity
theorem row052_nonnegative : 0≤row052 := by decide +kernel
#print axioms row052_nonnegative
noncomputable def row053 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row053 preparedMargin]]).head!.head!
theorem row053_weighted : row053=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row053 preparedMargin := by decide +kernel
#print axioms row053_weighted
theorem row053_identity : row053=NestedInteger.coefficientFrom (n := 0) 117 53 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 53 0 preparedMargin row053 IntegerBernsteinWeights117.row053
    (IntegerBernsteinTable.checked (n := 0) 117 53 0 117 preparedMargin IntegerBernsteinWeights117.row053 length_checked IntegerBernsteinWeights117.row053_identity) row053_weighted
#print axioms row053_identity
theorem row053_nonnegative : 0≤row053 := by decide +kernel
#print axioms row053_nonnegative
noncomputable def row054 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row054 preparedMargin]]).head!.head!
theorem row054_weighted : row054=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row054 preparedMargin := by decide +kernel
#print axioms row054_weighted
theorem row054_identity : row054=NestedInteger.coefficientFrom (n := 0) 117 54 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 54 0 preparedMargin row054 IntegerBernsteinWeights117.row054
    (IntegerBernsteinTable.checked (n := 0) 117 54 0 117 preparedMargin IntegerBernsteinWeights117.row054 length_checked IntegerBernsteinWeights117.row054_identity) row054_weighted
#print axioms row054_identity
theorem row054_nonnegative : 0≤row054 := by decide +kernel
#print axioms row054_nonnegative
noncomputable def row055 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row055 preparedMargin]]).head!.head!
theorem row055_weighted : row055=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row055 preparedMargin := by decide +kernel
#print axioms row055_weighted
theorem row055_identity : row055=NestedInteger.coefficientFrom (n := 0) 117 55 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 55 0 preparedMargin row055 IntegerBernsteinWeights117.row055
    (IntegerBernsteinTable.checked (n := 0) 117 55 0 117 preparedMargin IntegerBernsteinWeights117.row055 length_checked IntegerBernsteinWeights117.row055_identity) row055_weighted
#print axioms row055_identity
theorem row055_nonnegative : 0≤row055 := by decide +kernel
#print axioms row055_nonnegative
noncomputable def row056 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row056 preparedMargin]]).head!.head!
theorem row056_weighted : row056=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row056 preparedMargin := by decide +kernel
#print axioms row056_weighted
theorem row056_identity : row056=NestedInteger.coefficientFrom (n := 0) 117 56 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 56 0 preparedMargin row056 IntegerBernsteinWeights117.row056
    (IntegerBernsteinTable.checked (n := 0) 117 56 0 117 preparedMargin IntegerBernsteinWeights117.row056 length_checked IntegerBernsteinWeights117.row056_identity) row056_weighted
#print axioms row056_identity
theorem row056_nonnegative : 0≤row056 := by decide +kernel
#print axioms row056_nonnegative
noncomputable def row057 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row057 preparedMargin]]).head!.head!
theorem row057_weighted : row057=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row057 preparedMargin := by decide +kernel
#print axioms row057_weighted
theorem row057_identity : row057=NestedInteger.coefficientFrom (n := 0) 117 57 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 57 0 preparedMargin row057 IntegerBernsteinWeights117.row057
    (IntegerBernsteinTable.checked (n := 0) 117 57 0 117 preparedMargin IntegerBernsteinWeights117.row057 length_checked IntegerBernsteinWeights117.row057_identity) row057_weighted
#print axioms row057_identity
theorem row057_nonnegative : 0≤row057 := by decide +kernel
#print axioms row057_nonnegative
noncomputable def row058 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row058 preparedMargin]]).head!.head!
theorem row058_weighted : row058=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row058 preparedMargin := by decide +kernel
#print axioms row058_weighted
theorem row058_identity : row058=NestedInteger.coefficientFrom (n := 0) 117 58 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 58 0 preparedMargin row058 IntegerBernsteinWeights117.row058
    (IntegerBernsteinTable.checked (n := 0) 117 58 0 117 preparedMargin IntegerBernsteinWeights117.row058 length_checked IntegerBernsteinWeights117.row058_identity) row058_weighted
#print axioms row058_identity
theorem row058_nonnegative : 0≤row058 := by decide +kernel
#print axioms row058_nonnegative
noncomputable def row059 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row059 preparedMargin]]).head!.head!
theorem row059_weighted : row059=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row059 preparedMargin := by decide +kernel
#print axioms row059_weighted
theorem row059_identity : row059=NestedInteger.coefficientFrom (n := 0) 117 59 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 59 0 preparedMargin row059 IntegerBernsteinWeights117.row059
    (IntegerBernsteinTable.checked (n := 0) 117 59 0 117 preparedMargin IntegerBernsteinWeights117.row059 length_checked IntegerBernsteinWeights117.row059_identity) row059_weighted
#print axioms row059_identity
theorem row059_nonnegative : 0≤row059 := by decide +kernel
#print axioms row059_nonnegative
noncomputable def row060 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row060 preparedMargin]]).head!.head!
theorem row060_weighted : row060=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row060 preparedMargin := by decide +kernel
#print axioms row060_weighted
theorem row060_identity : row060=NestedInteger.coefficientFrom (n := 0) 117 60 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 60 0 preparedMargin row060 IntegerBernsteinWeights117.row060
    (IntegerBernsteinTable.checked (n := 0) 117 60 0 117 preparedMargin IntegerBernsteinWeights117.row060 length_checked IntegerBernsteinWeights117.row060_identity) row060_weighted
#print axioms row060_identity
theorem row060_nonnegative : 0≤row060 := by decide +kernel
#print axioms row060_nonnegative
noncomputable def row061 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row061 preparedMargin]]).head!.head!
theorem row061_weighted : row061=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row061 preparedMargin := by decide +kernel
#print axioms row061_weighted
theorem row061_identity : row061=NestedInteger.coefficientFrom (n := 0) 117 61 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 61 0 preparedMargin row061 IntegerBernsteinWeights117.row061
    (IntegerBernsteinTable.checked (n := 0) 117 61 0 117 preparedMargin IntegerBernsteinWeights117.row061 length_checked IntegerBernsteinWeights117.row061_identity) row061_weighted
#print axioms row061_identity
theorem row061_nonnegative : 0≤row061 := by decide +kernel
#print axioms row061_nonnegative
noncomputable def row062 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row062 preparedMargin]]).head!.head!
theorem row062_weighted : row062=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row062 preparedMargin := by decide +kernel
#print axioms row062_weighted
theorem row062_identity : row062=NestedInteger.coefficientFrom (n := 0) 117 62 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 62 0 preparedMargin row062 IntegerBernsteinWeights117.row062
    (IntegerBernsteinTable.checked (n := 0) 117 62 0 117 preparedMargin IntegerBernsteinWeights117.row062 length_checked IntegerBernsteinWeights117.row062_identity) row062_weighted
#print axioms row062_identity
theorem row062_nonnegative : 0≤row062 := by decide +kernel
#print axioms row062_nonnegative
noncomputable def row063 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row063 preparedMargin]]).head!.head!
theorem row063_weighted : row063=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row063 preparedMargin := by decide +kernel
#print axioms row063_weighted
theorem row063_identity : row063=NestedInteger.coefficientFrom (n := 0) 117 63 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 63 0 preparedMargin row063 IntegerBernsteinWeights117.row063
    (IntegerBernsteinTable.checked (n := 0) 117 63 0 117 preparedMargin IntegerBernsteinWeights117.row063 length_checked IntegerBernsteinWeights117.row063_identity) row063_weighted
#print axioms row063_identity
theorem row063_nonnegative : 0≤row063 := by decide +kernel
#print axioms row063_nonnegative
noncomputable def row064 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row064 preparedMargin]]).head!.head!
theorem row064_weighted : row064=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row064 preparedMargin := by decide +kernel
#print axioms row064_weighted
theorem row064_identity : row064=NestedInteger.coefficientFrom (n := 0) 117 64 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 64 0 preparedMargin row064 IntegerBernsteinWeights117.row064
    (IntegerBernsteinTable.checked (n := 0) 117 64 0 117 preparedMargin IntegerBernsteinWeights117.row064 length_checked IntegerBernsteinWeights117.row064_identity) row064_weighted
#print axioms row064_identity
theorem row064_nonnegative : 0≤row064 := by decide +kernel
#print axioms row064_nonnegative
noncomputable def row065 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row065 preparedMargin]]).head!.head!
theorem row065_weighted : row065=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row065 preparedMargin := by decide +kernel
#print axioms row065_weighted
theorem row065_identity : row065=NestedInteger.coefficientFrom (n := 0) 117 65 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 65 0 preparedMargin row065 IntegerBernsteinWeights117.row065
    (IntegerBernsteinTable.checked (n := 0) 117 65 0 117 preparedMargin IntegerBernsteinWeights117.row065 length_checked IntegerBernsteinWeights117.row065_identity) row065_weighted
#print axioms row065_identity
theorem row065_nonnegative : 0≤row065 := by decide +kernel
#print axioms row065_nonnegative
noncomputable def row066 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row066 preparedMargin]]).head!.head!
theorem row066_weighted : row066=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row066 preparedMargin := by decide +kernel
#print axioms row066_weighted
theorem row066_identity : row066=NestedInteger.coefficientFrom (n := 0) 117 66 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 66 0 preparedMargin row066 IntegerBernsteinWeights117.row066
    (IntegerBernsteinTable.checked (n := 0) 117 66 0 117 preparedMargin IntegerBernsteinWeights117.row066 length_checked IntegerBernsteinWeights117.row066_identity) row066_weighted
#print axioms row066_identity
theorem row066_nonnegative : 0≤row066 := by decide +kernel
#print axioms row066_nonnegative
noncomputable def row067 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row067 preparedMargin]]).head!.head!
theorem row067_weighted : row067=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row067 preparedMargin := by decide +kernel
#print axioms row067_weighted
theorem row067_identity : row067=NestedInteger.coefficientFrom (n := 0) 117 67 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 67 0 preparedMargin row067 IntegerBernsteinWeights117.row067
    (IntegerBernsteinTable.checked (n := 0) 117 67 0 117 preparedMargin IntegerBernsteinWeights117.row067 length_checked IntegerBernsteinWeights117.row067_identity) row067_weighted
#print axioms row067_identity
theorem row067_nonnegative : 0≤row067 := by decide +kernel
#print axioms row067_nonnegative
noncomputable def row068 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row068 preparedMargin]]).head!.head!
theorem row068_weighted : row068=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row068 preparedMargin := by decide +kernel
#print axioms row068_weighted
theorem row068_identity : row068=NestedInteger.coefficientFrom (n := 0) 117 68 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 68 0 preparedMargin row068 IntegerBernsteinWeights117.row068
    (IntegerBernsteinTable.checked (n := 0) 117 68 0 117 preparedMargin IntegerBernsteinWeights117.row068 length_checked IntegerBernsteinWeights117.row068_identity) row068_weighted
#print axioms row068_identity
theorem row068_nonnegative : 0≤row068 := by decide +kernel
#print axioms row068_nonnegative
noncomputable def row069 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row069 preparedMargin]]).head!.head!
theorem row069_weighted : row069=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row069 preparedMargin := by decide +kernel
#print axioms row069_weighted
theorem row069_identity : row069=NestedInteger.coefficientFrom (n := 0) 117 69 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 69 0 preparedMargin row069 IntegerBernsteinWeights117.row069
    (IntegerBernsteinTable.checked (n := 0) 117 69 0 117 preparedMargin IntegerBernsteinWeights117.row069 length_checked IntegerBernsteinWeights117.row069_identity) row069_weighted
#print axioms row069_identity
theorem row069_nonnegative : 0≤row069 := by decide +kernel
#print axioms row069_nonnegative
noncomputable def row070 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row070 preparedMargin]]).head!.head!
theorem row070_weighted : row070=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row070 preparedMargin := by decide +kernel
#print axioms row070_weighted
theorem row070_identity : row070=NestedInteger.coefficientFrom (n := 0) 117 70 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 70 0 preparedMargin row070 IntegerBernsteinWeights117.row070
    (IntegerBernsteinTable.checked (n := 0) 117 70 0 117 preparedMargin IntegerBernsteinWeights117.row070 length_checked IntegerBernsteinWeights117.row070_identity) row070_weighted
#print axioms row070_identity
theorem row070_nonnegative : 0≤row070 := by decide +kernel
#print axioms row070_nonnegative
noncomputable def row071 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row071 preparedMargin]]).head!.head!
theorem row071_weighted : row071=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row071 preparedMargin := by decide +kernel
#print axioms row071_weighted
theorem row071_identity : row071=NestedInteger.coefficientFrom (n := 0) 117 71 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 71 0 preparedMargin row071 IntegerBernsteinWeights117.row071
    (IntegerBernsteinTable.checked (n := 0) 117 71 0 117 preparedMargin IntegerBernsteinWeights117.row071 length_checked IntegerBernsteinWeights117.row071_identity) row071_weighted
#print axioms row071_identity
theorem row071_nonnegative : 0≤row071 := by decide +kernel
#print axioms row071_nonnegative
noncomputable def row072 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row072 preparedMargin]]).head!.head!
theorem row072_weighted : row072=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row072 preparedMargin := by decide +kernel
#print axioms row072_weighted
theorem row072_identity : row072=NestedInteger.coefficientFrom (n := 0) 117 72 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 72 0 preparedMargin row072 IntegerBernsteinWeights117.row072
    (IntegerBernsteinTable.checked (n := 0) 117 72 0 117 preparedMargin IntegerBernsteinWeights117.row072 length_checked IntegerBernsteinWeights117.row072_identity) row072_weighted
#print axioms row072_identity
theorem row072_nonnegative : 0≤row072 := by decide +kernel
#print axioms row072_nonnegative
noncomputable def row073 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row073 preparedMargin]]).head!.head!
theorem row073_weighted : row073=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row073 preparedMargin := by decide +kernel
#print axioms row073_weighted
theorem row073_identity : row073=NestedInteger.coefficientFrom (n := 0) 117 73 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 73 0 preparedMargin row073 IntegerBernsteinWeights117.row073
    (IntegerBernsteinTable.checked (n := 0) 117 73 0 117 preparedMargin IntegerBernsteinWeights117.row073 length_checked IntegerBernsteinWeights117.row073_identity) row073_weighted
#print axioms row073_identity
theorem row073_nonnegative : 0≤row073 := by decide +kernel
#print axioms row073_nonnegative
noncomputable def row074 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row074 preparedMargin]]).head!.head!
theorem row074_weighted : row074=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row074 preparedMargin := by decide +kernel
#print axioms row074_weighted
theorem row074_identity : row074=NestedInteger.coefficientFrom (n := 0) 117 74 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 74 0 preparedMargin row074 IntegerBernsteinWeights117.row074
    (IntegerBernsteinTable.checked (n := 0) 117 74 0 117 preparedMargin IntegerBernsteinWeights117.row074 length_checked IntegerBernsteinWeights117.row074_identity) row074_weighted
#print axioms row074_identity
theorem row074_nonnegative : 0≤row074 := by decide +kernel
#print axioms row074_nonnegative
noncomputable def row075 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row075 preparedMargin]]).head!.head!
theorem row075_weighted : row075=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row075 preparedMargin := by decide +kernel
#print axioms row075_weighted
theorem row075_identity : row075=NestedInteger.coefficientFrom (n := 0) 117 75 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 75 0 preparedMargin row075 IntegerBernsteinWeights117.row075
    (IntegerBernsteinTable.checked (n := 0) 117 75 0 117 preparedMargin IntegerBernsteinWeights117.row075 length_checked IntegerBernsteinWeights117.row075_identity) row075_weighted
#print axioms row075_identity
theorem row075_nonnegative : 0≤row075 := by decide +kernel
#print axioms row075_nonnegative
noncomputable def row076 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row076 preparedMargin]]).head!.head!
theorem row076_weighted : row076=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row076 preparedMargin := by decide +kernel
#print axioms row076_weighted
theorem row076_identity : row076=NestedInteger.coefficientFrom (n := 0) 117 76 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 76 0 preparedMargin row076 IntegerBernsteinWeights117.row076
    (IntegerBernsteinTable.checked (n := 0) 117 76 0 117 preparedMargin IntegerBernsteinWeights117.row076 length_checked IntegerBernsteinWeights117.row076_identity) row076_weighted
#print axioms row076_identity
theorem row076_nonnegative : 0≤row076 := by decide +kernel
#print axioms row076_nonnegative
noncomputable def row077 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row077 preparedMargin]]).head!.head!
theorem row077_weighted : row077=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row077 preparedMargin := by decide +kernel
#print axioms row077_weighted
theorem row077_identity : row077=NestedInteger.coefficientFrom (n := 0) 117 77 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 77 0 preparedMargin row077 IntegerBernsteinWeights117.row077
    (IntegerBernsteinTable.checked (n := 0) 117 77 0 117 preparedMargin IntegerBernsteinWeights117.row077 length_checked IntegerBernsteinWeights117.row077_identity) row077_weighted
#print axioms row077_identity
theorem row077_nonnegative : 0≤row077 := by decide +kernel
#print axioms row077_nonnegative
noncomputable def row078 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row078 preparedMargin]]).head!.head!
theorem row078_weighted : row078=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row078 preparedMargin := by decide +kernel
#print axioms row078_weighted
theorem row078_identity : row078=NestedInteger.coefficientFrom (n := 0) 117 78 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 78 0 preparedMargin row078 IntegerBernsteinWeights117.row078
    (IntegerBernsteinTable.checked (n := 0) 117 78 0 117 preparedMargin IntegerBernsteinWeights117.row078 length_checked IntegerBernsteinWeights117.row078_identity) row078_weighted
#print axioms row078_identity
theorem row078_nonnegative : 0≤row078 := by decide +kernel
#print axioms row078_nonnegative
noncomputable def row079 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row079 preparedMargin]]).head!.head!
theorem row079_weighted : row079=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row079 preparedMargin := by decide +kernel
#print axioms row079_weighted
theorem row079_identity : row079=NestedInteger.coefficientFrom (n := 0) 117 79 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 79 0 preparedMargin row079 IntegerBernsteinWeights117.row079
    (IntegerBernsteinTable.checked (n := 0) 117 79 0 117 preparedMargin IntegerBernsteinWeights117.row079 length_checked IntegerBernsteinWeights117.row079_identity) row079_weighted
#print axioms row079_identity
theorem row079_nonnegative : 0≤row079 := by decide +kernel
#print axioms row079_nonnegative
noncomputable def row080 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row080 preparedMargin]]).head!.head!
theorem row080_weighted : row080=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row080 preparedMargin := by decide +kernel
#print axioms row080_weighted
theorem row080_identity : row080=NestedInteger.coefficientFrom (n := 0) 117 80 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 80 0 preparedMargin row080 IntegerBernsteinWeights117.row080
    (IntegerBernsteinTable.checked (n := 0) 117 80 0 117 preparedMargin IntegerBernsteinWeights117.row080 length_checked IntegerBernsteinWeights117.row080_identity) row080_weighted
#print axioms row080_identity
theorem row080_nonnegative : 0≤row080 := by decide +kernel
#print axioms row080_nonnegative
noncomputable def row081 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row081 preparedMargin]]).head!.head!
theorem row081_weighted : row081=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row081 preparedMargin := by decide +kernel
#print axioms row081_weighted
theorem row081_identity : row081=NestedInteger.coefficientFrom (n := 0) 117 81 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 81 0 preparedMargin row081 IntegerBernsteinWeights117.row081
    (IntegerBernsteinTable.checked (n := 0) 117 81 0 117 preparedMargin IntegerBernsteinWeights117.row081 length_checked IntegerBernsteinWeights117.row081_identity) row081_weighted
#print axioms row081_identity
theorem row081_nonnegative : 0≤row081 := by decide +kernel
#print axioms row081_nonnegative
noncomputable def row082 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row082 preparedMargin]]).head!.head!
theorem row082_weighted : row082=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row082 preparedMargin := by decide +kernel
#print axioms row082_weighted
theorem row082_identity : row082=NestedInteger.coefficientFrom (n := 0) 117 82 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 82 0 preparedMargin row082 IntegerBernsteinWeights117.row082
    (IntegerBernsteinTable.checked (n := 0) 117 82 0 117 preparedMargin IntegerBernsteinWeights117.row082 length_checked IntegerBernsteinWeights117.row082_identity) row082_weighted
#print axioms row082_identity
theorem row082_nonnegative : 0≤row082 := by decide +kernel
#print axioms row082_nonnegative
noncomputable def row083 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row083 preparedMargin]]).head!.head!
theorem row083_weighted : row083=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row083 preparedMargin := by decide +kernel
#print axioms row083_weighted
theorem row083_identity : row083=NestedInteger.coefficientFrom (n := 0) 117 83 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 83 0 preparedMargin row083 IntegerBernsteinWeights117.row083
    (IntegerBernsteinTable.checked (n := 0) 117 83 0 117 preparedMargin IntegerBernsteinWeights117.row083 length_checked IntegerBernsteinWeights117.row083_identity) row083_weighted
#print axioms row083_identity
theorem row083_nonnegative : 0≤row083 := by decide +kernel
#print axioms row083_nonnegative
noncomputable def row084 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row084 preparedMargin]]).head!.head!
theorem row084_weighted : row084=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row084 preparedMargin := by decide +kernel
#print axioms row084_weighted
theorem row084_identity : row084=NestedInteger.coefficientFrom (n := 0) 117 84 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 84 0 preparedMargin row084 IntegerBernsteinWeights117.row084
    (IntegerBernsteinTable.checked (n := 0) 117 84 0 117 preparedMargin IntegerBernsteinWeights117.row084 length_checked IntegerBernsteinWeights117.row084_identity) row084_weighted
#print axioms row084_identity
theorem row084_nonnegative : 0≤row084 := by decide +kernel
#print axioms row084_nonnegative
noncomputable def row085 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row085 preparedMargin]]).head!.head!
theorem row085_weighted : row085=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row085 preparedMargin := by decide +kernel
#print axioms row085_weighted
theorem row085_identity : row085=NestedInteger.coefficientFrom (n := 0) 117 85 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 85 0 preparedMargin row085 IntegerBernsteinWeights117.row085
    (IntegerBernsteinTable.checked (n := 0) 117 85 0 117 preparedMargin IntegerBernsteinWeights117.row085 length_checked IntegerBernsteinWeights117.row085_identity) row085_weighted
#print axioms row085_identity
theorem row085_nonnegative : 0≤row085 := by decide +kernel
#print axioms row085_nonnegative
noncomputable def row086 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row086 preparedMargin]]).head!.head!
theorem row086_weighted : row086=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row086 preparedMargin := by decide +kernel
#print axioms row086_weighted
theorem row086_identity : row086=NestedInteger.coefficientFrom (n := 0) 117 86 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 86 0 preparedMargin row086 IntegerBernsteinWeights117.row086
    (IntegerBernsteinTable.checked (n := 0) 117 86 0 117 preparedMargin IntegerBernsteinWeights117.row086 length_checked IntegerBernsteinWeights117.row086_identity) row086_weighted
#print axioms row086_identity
theorem row086_nonnegative : 0≤row086 := by decide +kernel
#print axioms row086_nonnegative
noncomputable def row087 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row087 preparedMargin]]).head!.head!
theorem row087_weighted : row087=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row087 preparedMargin := by decide +kernel
#print axioms row087_weighted
theorem row087_identity : row087=NestedInteger.coefficientFrom (n := 0) 117 87 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 87 0 preparedMargin row087 IntegerBernsteinWeights117.row087
    (IntegerBernsteinTable.checked (n := 0) 117 87 0 117 preparedMargin IntegerBernsteinWeights117.row087 length_checked IntegerBernsteinWeights117.row087_identity) row087_weighted
#print axioms row087_identity
theorem row087_nonnegative : 0≤row087 := by decide +kernel
#print axioms row087_nonnegative
noncomputable def row088 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row088 preparedMargin]]).head!.head!
theorem row088_weighted : row088=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row088 preparedMargin := by decide +kernel
#print axioms row088_weighted
theorem row088_identity : row088=NestedInteger.coefficientFrom (n := 0) 117 88 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 88 0 preparedMargin row088 IntegerBernsteinWeights117.row088
    (IntegerBernsteinTable.checked (n := 0) 117 88 0 117 preparedMargin IntegerBernsteinWeights117.row088 length_checked IntegerBernsteinWeights117.row088_identity) row088_weighted
#print axioms row088_identity
theorem row088_nonnegative : 0≤row088 := by decide +kernel
#print axioms row088_nonnegative
noncomputable def row089 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row089 preparedMargin]]).head!.head!
theorem row089_weighted : row089=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row089 preparedMargin := by decide +kernel
#print axioms row089_weighted
theorem row089_identity : row089=NestedInteger.coefficientFrom (n := 0) 117 89 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 89 0 preparedMargin row089 IntegerBernsteinWeights117.row089
    (IntegerBernsteinTable.checked (n := 0) 117 89 0 117 preparedMargin IntegerBernsteinWeights117.row089 length_checked IntegerBernsteinWeights117.row089_identity) row089_weighted
#print axioms row089_identity
theorem row089_nonnegative : 0≤row089 := by decide +kernel
#print axioms row089_nonnegative
noncomputable def row090 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row090 preparedMargin]]).head!.head!
theorem row090_weighted : row090=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row090 preparedMargin := by decide +kernel
#print axioms row090_weighted
theorem row090_identity : row090=NestedInteger.coefficientFrom (n := 0) 117 90 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 90 0 preparedMargin row090 IntegerBernsteinWeights117.row090
    (IntegerBernsteinTable.checked (n := 0) 117 90 0 117 preparedMargin IntegerBernsteinWeights117.row090 length_checked IntegerBernsteinWeights117.row090_identity) row090_weighted
#print axioms row090_identity
theorem row090_nonnegative : 0≤row090 := by decide +kernel
#print axioms row090_nonnegative
noncomputable def row091 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row091 preparedMargin]]).head!.head!
theorem row091_weighted : row091=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row091 preparedMargin := by decide +kernel
#print axioms row091_weighted
theorem row091_identity : row091=NestedInteger.coefficientFrom (n := 0) 117 91 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 91 0 preparedMargin row091 IntegerBernsteinWeights117.row091
    (IntegerBernsteinTable.checked (n := 0) 117 91 0 117 preparedMargin IntegerBernsteinWeights117.row091 length_checked IntegerBernsteinWeights117.row091_identity) row091_weighted
#print axioms row091_identity
theorem row091_nonnegative : 0≤row091 := by decide +kernel
#print axioms row091_nonnegative
noncomputable def row092 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row092 preparedMargin]]).head!.head!
theorem row092_weighted : row092=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row092 preparedMargin := by decide +kernel
#print axioms row092_weighted
theorem row092_identity : row092=NestedInteger.coefficientFrom (n := 0) 117 92 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 92 0 preparedMargin row092 IntegerBernsteinWeights117.row092
    (IntegerBernsteinTable.checked (n := 0) 117 92 0 117 preparedMargin IntegerBernsteinWeights117.row092 length_checked IntegerBernsteinWeights117.row092_identity) row092_weighted
#print axioms row092_identity
theorem row092_nonnegative : 0≤row092 := by decide +kernel
#print axioms row092_nonnegative
noncomputable def row093 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row093 preparedMargin]]).head!.head!
theorem row093_weighted : row093=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row093 preparedMargin := by decide +kernel
#print axioms row093_weighted
theorem row093_identity : row093=NestedInteger.coefficientFrom (n := 0) 117 93 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 93 0 preparedMargin row093 IntegerBernsteinWeights117.row093
    (IntegerBernsteinTable.checked (n := 0) 117 93 0 117 preparedMargin IntegerBernsteinWeights117.row093 length_checked IntegerBernsteinWeights117.row093_identity) row093_weighted
#print axioms row093_identity
theorem row093_nonnegative : 0≤row093 := by decide +kernel
#print axioms row093_nonnegative
noncomputable def row094 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row094 preparedMargin]]).head!.head!
theorem row094_weighted : row094=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row094 preparedMargin := by decide +kernel
#print axioms row094_weighted
theorem row094_identity : row094=NestedInteger.coefficientFrom (n := 0) 117 94 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 94 0 preparedMargin row094 IntegerBernsteinWeights117.row094
    (IntegerBernsteinTable.checked (n := 0) 117 94 0 117 preparedMargin IntegerBernsteinWeights117.row094 length_checked IntegerBernsteinWeights117.row094_identity) row094_weighted
#print axioms row094_identity
theorem row094_nonnegative : 0≤row094 := by decide +kernel
#print axioms row094_nonnegative
noncomputable def row095 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row095 preparedMargin]]).head!.head!
theorem row095_weighted : row095=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row095 preparedMargin := by decide +kernel
#print axioms row095_weighted
theorem row095_identity : row095=NestedInteger.coefficientFrom (n := 0) 117 95 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 95 0 preparedMargin row095 IntegerBernsteinWeights117.row095
    (IntegerBernsteinTable.checked (n := 0) 117 95 0 117 preparedMargin IntegerBernsteinWeights117.row095 length_checked IntegerBernsteinWeights117.row095_identity) row095_weighted
#print axioms row095_identity
theorem row095_nonnegative : 0≤row095 := by decide +kernel
#print axioms row095_nonnegative
noncomputable def row096 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row096 preparedMargin]]).head!.head!
theorem row096_weighted : row096=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row096 preparedMargin := by decide +kernel
#print axioms row096_weighted
theorem row096_identity : row096=NestedInteger.coefficientFrom (n := 0) 117 96 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 96 0 preparedMargin row096 IntegerBernsteinWeights117.row096
    (IntegerBernsteinTable.checked (n := 0) 117 96 0 117 preparedMargin IntegerBernsteinWeights117.row096 length_checked IntegerBernsteinWeights117.row096_identity) row096_weighted
#print axioms row096_identity
theorem row096_nonnegative : 0≤row096 := by decide +kernel
#print axioms row096_nonnegative
noncomputable def row097 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row097 preparedMargin]]).head!.head!
theorem row097_weighted : row097=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row097 preparedMargin := by decide +kernel
#print axioms row097_weighted
theorem row097_identity : row097=NestedInteger.coefficientFrom (n := 0) 117 97 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 97 0 preparedMargin row097 IntegerBernsteinWeights117.row097
    (IntegerBernsteinTable.checked (n := 0) 117 97 0 117 preparedMargin IntegerBernsteinWeights117.row097 length_checked IntegerBernsteinWeights117.row097_identity) row097_weighted
#print axioms row097_identity
theorem row097_nonnegative : 0≤row097 := by decide +kernel
#print axioms row097_nonnegative
noncomputable def row098 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row098 preparedMargin]]).head!.head!
theorem row098_weighted : row098=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row098 preparedMargin := by decide +kernel
#print axioms row098_weighted
theorem row098_identity : row098=NestedInteger.coefficientFrom (n := 0) 117 98 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 98 0 preparedMargin row098 IntegerBernsteinWeights117.row098
    (IntegerBernsteinTable.checked (n := 0) 117 98 0 117 preparedMargin IntegerBernsteinWeights117.row098 length_checked IntegerBernsteinWeights117.row098_identity) row098_weighted
#print axioms row098_identity
theorem row098_nonnegative : 0≤row098 := by decide +kernel
#print axioms row098_nonnegative
noncomputable def row099 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row099 preparedMargin]]).head!.head!
theorem row099_weighted : row099=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row099 preparedMargin := by decide +kernel
#print axioms row099_weighted
theorem row099_identity : row099=NestedInteger.coefficientFrom (n := 0) 117 99 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 99 0 preparedMargin row099 IntegerBernsteinWeights117.row099
    (IntegerBernsteinTable.checked (n := 0) 117 99 0 117 preparedMargin IntegerBernsteinWeights117.row099 length_checked IntegerBernsteinWeights117.row099_identity) row099_weighted
#print axioms row099_identity
theorem row099_nonnegative : 0≤row099 := by decide +kernel
#print axioms row099_nonnegative
noncomputable def row100 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row100 preparedMargin]]).head!.head!
theorem row100_weighted : row100=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row100 preparedMargin := by decide +kernel
#print axioms row100_weighted
theorem row100_identity : row100=NestedInteger.coefficientFrom (n := 0) 117 100 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 100 0 preparedMargin row100 IntegerBernsteinWeights117.row100
    (IntegerBernsteinTable.checked (n := 0) 117 100 0 117 preparedMargin IntegerBernsteinWeights117.row100 length_checked IntegerBernsteinWeights117.row100_identity) row100_weighted
#print axioms row100_identity
theorem row100_nonnegative : 0≤row100 := by decide +kernel
#print axioms row100_nonnegative
noncomputable def row101 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row101 preparedMargin]]).head!.head!
theorem row101_weighted : row101=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row101 preparedMargin := by decide +kernel
#print axioms row101_weighted
theorem row101_identity : row101=NestedInteger.coefficientFrom (n := 0) 117 101 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 101 0 preparedMargin row101 IntegerBernsteinWeights117.row101
    (IntegerBernsteinTable.checked (n := 0) 117 101 0 117 preparedMargin IntegerBernsteinWeights117.row101 length_checked IntegerBernsteinWeights117.row101_identity) row101_weighted
#print axioms row101_identity
theorem row101_nonnegative : 0≤row101 := by decide +kernel
#print axioms row101_nonnegative
noncomputable def row102 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row102 preparedMargin]]).head!.head!
theorem row102_weighted : row102=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row102 preparedMargin := by decide +kernel
#print axioms row102_weighted
theorem row102_identity : row102=NestedInteger.coefficientFrom (n := 0) 117 102 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 102 0 preparedMargin row102 IntegerBernsteinWeights117.row102
    (IntegerBernsteinTable.checked (n := 0) 117 102 0 117 preparedMargin IntegerBernsteinWeights117.row102 length_checked IntegerBernsteinWeights117.row102_identity) row102_weighted
#print axioms row102_identity
theorem row102_nonnegative : 0≤row102 := by decide +kernel
#print axioms row102_nonnegative
noncomputable def row103 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row103 preparedMargin]]).head!.head!
theorem row103_weighted : row103=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row103 preparedMargin := by decide +kernel
#print axioms row103_weighted
theorem row103_identity : row103=NestedInteger.coefficientFrom (n := 0) 117 103 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 103 0 preparedMargin row103 IntegerBernsteinWeights117.row103
    (IntegerBernsteinTable.checked (n := 0) 117 103 0 117 preparedMargin IntegerBernsteinWeights117.row103 length_checked IntegerBernsteinWeights117.row103_identity) row103_weighted
#print axioms row103_identity
theorem row103_nonnegative : 0≤row103 := by decide +kernel
#print axioms row103_nonnegative
noncomputable def row104 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row104 preparedMargin]]).head!.head!
theorem row104_weighted : row104=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row104 preparedMargin := by decide +kernel
#print axioms row104_weighted
theorem row104_identity : row104=NestedInteger.coefficientFrom (n := 0) 117 104 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 104 0 preparedMargin row104 IntegerBernsteinWeights117.row104
    (IntegerBernsteinTable.checked (n := 0) 117 104 0 117 preparedMargin IntegerBernsteinWeights117.row104 length_checked IntegerBernsteinWeights117.row104_identity) row104_weighted
#print axioms row104_identity
theorem row104_nonnegative : 0≤row104 := by decide +kernel
#print axioms row104_nonnegative
noncomputable def row105 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row105 preparedMargin]]).head!.head!
theorem row105_weighted : row105=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row105 preparedMargin := by decide +kernel
#print axioms row105_weighted
theorem row105_identity : row105=NestedInteger.coefficientFrom (n := 0) 117 105 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 105 0 preparedMargin row105 IntegerBernsteinWeights117.row105
    (IntegerBernsteinTable.checked (n := 0) 117 105 0 117 preparedMargin IntegerBernsteinWeights117.row105 length_checked IntegerBernsteinWeights117.row105_identity) row105_weighted
#print axioms row105_identity
theorem row105_nonnegative : 0≤row105 := by decide +kernel
#print axioms row105_nonnegative
noncomputable def row106 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row106 preparedMargin]]).head!.head!
theorem row106_weighted : row106=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row106 preparedMargin := by decide +kernel
#print axioms row106_weighted
theorem row106_identity : row106=NestedInteger.coefficientFrom (n := 0) 117 106 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 106 0 preparedMargin row106 IntegerBernsteinWeights117.row106
    (IntegerBernsteinTable.checked (n := 0) 117 106 0 117 preparedMargin IntegerBernsteinWeights117.row106 length_checked IntegerBernsteinWeights117.row106_identity) row106_weighted
#print axioms row106_identity
theorem row106_nonnegative : 0≤row106 := by decide +kernel
#print axioms row106_nonnegative
noncomputable def row107 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row107 preparedMargin]]).head!.head!
theorem row107_weighted : row107=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row107 preparedMargin := by decide +kernel
#print axioms row107_weighted
theorem row107_identity : row107=NestedInteger.coefficientFrom (n := 0) 117 107 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 107 0 preparedMargin row107 IntegerBernsteinWeights117.row107
    (IntegerBernsteinTable.checked (n := 0) 117 107 0 117 preparedMargin IntegerBernsteinWeights117.row107 length_checked IntegerBernsteinWeights117.row107_identity) row107_weighted
#print axioms row107_identity
theorem row107_nonnegative : 0≤row107 := by decide +kernel
#print axioms row107_nonnegative
noncomputable def row108 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row108 preparedMargin]]).head!.head!
theorem row108_weighted : row108=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row108 preparedMargin := by decide +kernel
#print axioms row108_weighted
theorem row108_identity : row108=NestedInteger.coefficientFrom (n := 0) 117 108 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 108 0 preparedMargin row108 IntegerBernsteinWeights117.row108
    (IntegerBernsteinTable.checked (n := 0) 117 108 0 117 preparedMargin IntegerBernsteinWeights117.row108 length_checked IntegerBernsteinWeights117.row108_identity) row108_weighted
#print axioms row108_identity
theorem row108_nonnegative : 0≤row108 := by decide +kernel
#print axioms row108_nonnegative
noncomputable def row109 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row109 preparedMargin]]).head!.head!
theorem row109_weighted : row109=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row109 preparedMargin := by decide +kernel
#print axioms row109_weighted
theorem row109_identity : row109=NestedInteger.coefficientFrom (n := 0) 117 109 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 109 0 preparedMargin row109 IntegerBernsteinWeights117.row109
    (IntegerBernsteinTable.checked (n := 0) 117 109 0 117 preparedMargin IntegerBernsteinWeights117.row109 length_checked IntegerBernsteinWeights117.row109_identity) row109_weighted
#print axioms row109_identity
theorem row109_nonnegative : 0≤row109 := by decide +kernel
#print axioms row109_nonnegative
noncomputable def row110 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row110 preparedMargin]]).head!.head!
theorem row110_weighted : row110=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row110 preparedMargin := by decide +kernel
#print axioms row110_weighted
theorem row110_identity : row110=NestedInteger.coefficientFrom (n := 0) 117 110 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 110 0 preparedMargin row110 IntegerBernsteinWeights117.row110
    (IntegerBernsteinTable.checked (n := 0) 117 110 0 117 preparedMargin IntegerBernsteinWeights117.row110 length_checked IntegerBernsteinWeights117.row110_identity) row110_weighted
#print axioms row110_identity
theorem row110_nonnegative : 0≤row110 := by decide +kernel
#print axioms row110_nonnegative
noncomputable def row111 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row111 preparedMargin]]).head!.head!
theorem row111_weighted : row111=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row111 preparedMargin := by decide +kernel
#print axioms row111_weighted
theorem row111_identity : row111=NestedInteger.coefficientFrom (n := 0) 117 111 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 111 0 preparedMargin row111 IntegerBernsteinWeights117.row111
    (IntegerBernsteinTable.checked (n := 0) 117 111 0 117 preparedMargin IntegerBernsteinWeights117.row111 length_checked IntegerBernsteinWeights117.row111_identity) row111_weighted
#print axioms row111_identity
theorem row111_nonnegative : 0≤row111 := by decide +kernel
#print axioms row111_nonnegative
noncomputable def row112 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row112 preparedMargin]]).head!.head!
theorem row112_weighted : row112=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row112 preparedMargin := by decide +kernel
#print axioms row112_weighted
theorem row112_identity : row112=NestedInteger.coefficientFrom (n := 0) 117 112 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 112 0 preparedMargin row112 IntegerBernsteinWeights117.row112
    (IntegerBernsteinTable.checked (n := 0) 117 112 0 117 preparedMargin IntegerBernsteinWeights117.row112 length_checked IntegerBernsteinWeights117.row112_identity) row112_weighted
#print axioms row112_identity
theorem row112_nonnegative : 0≤row112 := by decide +kernel
#print axioms row112_nonnegative
noncomputable def row113 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row113 preparedMargin]]).head!.head!
theorem row113_weighted : row113=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row113 preparedMargin := by decide +kernel
#print axioms row113_weighted
theorem row113_identity : row113=NestedInteger.coefficientFrom (n := 0) 117 113 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 113 0 preparedMargin row113 IntegerBernsteinWeights117.row113
    (IntegerBernsteinTable.checked (n := 0) 117 113 0 117 preparedMargin IntegerBernsteinWeights117.row113 length_checked IntegerBernsteinWeights117.row113_identity) row113_weighted
#print axioms row113_identity
theorem row113_nonnegative : 0≤row113 := by decide +kernel
#print axioms row113_nonnegative
noncomputable def row114 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row114 preparedMargin]]).head!.head!
theorem row114_weighted : row114=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row114 preparedMargin := by decide +kernel
#print axioms row114_weighted
theorem row114_identity : row114=NestedInteger.coefficientFrom (n := 0) 117 114 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 114 0 preparedMargin row114 IntegerBernsteinWeights117.row114
    (IntegerBernsteinTable.checked (n := 0) 117 114 0 117 preparedMargin IntegerBernsteinWeights117.row114 length_checked IntegerBernsteinWeights117.row114_identity) row114_weighted
#print axioms row114_identity
theorem row114_nonnegative : 0≤row114 := by decide +kernel
#print axioms row114_nonnegative
noncomputable def row115 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row115 preparedMargin]]).head!.head!
theorem row115_weighted : row115=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row115 preparedMargin := by decide +kernel
#print axioms row115_weighted
theorem row115_identity : row115=NestedInteger.coefficientFrom (n := 0) 117 115 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 115 0 preparedMargin row115 IntegerBernsteinWeights117.row115
    (IntegerBernsteinTable.checked (n := 0) 117 115 0 117 preparedMargin IntegerBernsteinWeights117.row115 length_checked IntegerBernsteinWeights117.row115_identity) row115_weighted
#print axioms row115_identity
theorem row115_nonnegative : 0≤row115 := by decide +kernel
#print axioms row115_nonnegative
noncomputable def row116 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row116 preparedMargin]]).head!.head!
theorem row116_weighted : row116=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row116 preparedMargin := by decide +kernel
#print axioms row116_weighted
theorem row116_identity : row116=NestedInteger.coefficientFrom (n := 0) 117 116 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 116 0 preparedMargin row116 IntegerBernsteinWeights117.row116
    (IntegerBernsteinTable.checked (n := 0) 117 116 0 117 preparedMargin IntegerBernsteinWeights117.row116 length_checked IntegerBernsteinWeights117.row116_identity) row116_weighted
#print axioms row116_identity
theorem row116_nonnegative : 0≤row116 := by decide +kernel
#print axioms row116_nonnegative
noncomputable def row117 : ℤ := (rg_closed_integer_row% [[IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row117 preparedMargin]]).head!.head!
theorem row117_weighted : row117=IntegerWeightedBernstein.applyWeights (n := 0) IntegerBernsteinWeights117.row117 preparedMargin := by decide +kernel
#print axioms row117_weighted
theorem row117_identity : row117=NestedInteger.coefficientFrom (n := 0) 117 117 0 preparedMargin :=
  IntegerWeightedBernstein.checked (n := 0) 117 117 0 preparedMargin row117 IntegerBernsteinWeights117.row117
    (IntegerBernsteinTable.checked (n := 0) 117 117 0 117 preparedMargin IntegerBernsteinWeights117.row117 length_checked IntegerBernsteinWeights117.row117_identity) row117_weighted
#print axioms row117_identity
theorem row117_nonnegative : 0≤row117 := by decide +kernel
#print axioms row117_nonnegative
noncomputable def rows : Fin (117+1) → ℤ := ![row000,row001,row002,row003,row004,row005,row006,row007,row008,row009,row010,row011,row012,row013,row014,row015,row016,row017,row018,row019,row020,row021,row022,row023,row024,row025,row026,row027,row028,row029,row030,row031,row032,row033,row034,row035,row036,row037,row038,row039,row040,row041,row042,row043,row044,row045,row046,row047,row048,row049,row050,row051,row052,row053,row054,row055,row056,row057,row058,row059,row060,row061,row062,row063,row064,row065,row066,row067,row068,row069,row070,row071,row072,row073,row074,row075,row076,row077,row078,row079,row080,row081,row082,row083,row084,row085,row086,row087,row088,row089,row090,row091,row092,row093,row094,row095,row096,row097,row098,row099,row100,row101,row102,row103,row104,row105,row106,row107,row108,row109,row110,row111,row112,row113,row114,row115,row116,row117]
theorem weighted_margin_sign : IntegerPolynomialPaymentCell.positive preparedMargin=true := by
  apply IntegerBernsteinScalarRows.checked preparedMargin 117 length_checked rows
  · intro j
    fin_cases j
    · exact row000_identity
    · exact row001_identity
    · exact row002_identity
    · exact row003_identity
    · exact row004_identity
    · exact row005_identity
    · exact row006_identity
    · exact row007_identity
    · exact row008_identity
    · exact row009_identity
    · exact row010_identity
    · exact row011_identity
    · exact row012_identity
    · exact row013_identity
    · exact row014_identity
    · exact row015_identity
    · exact row016_identity
    · exact row017_identity
    · exact row018_identity
    · exact row019_identity
    · exact row020_identity
    · exact row021_identity
    · exact row022_identity
    · exact row023_identity
    · exact row024_identity
    · exact row025_identity
    · exact row026_identity
    · exact row027_identity
    · exact row028_identity
    · exact row029_identity
    · exact row030_identity
    · exact row031_identity
    · exact row032_identity
    · exact row033_identity
    · exact row034_identity
    · exact row035_identity
    · exact row036_identity
    · exact row037_identity
    · exact row038_identity
    · exact row039_identity
    · exact row040_identity
    · exact row041_identity
    · exact row042_identity
    · exact row043_identity
    · exact row044_identity
    · exact row045_identity
    · exact row046_identity
    · exact row047_identity
    · exact row048_identity
    · exact row049_identity
    · exact row050_identity
    · exact row051_identity
    · exact row052_identity
    · exact row053_identity
    · exact row054_identity
    · exact row055_identity
    · exact row056_identity
    · exact row057_identity
    · exact row058_identity
    · exact row059_identity
    · exact row060_identity
    · exact row061_identity
    · exact row062_identity
    · exact row063_identity
    · exact row064_identity
    · exact row065_identity
    · exact row066_identity
    · exact row067_identity
    · exact row068_identity
    · exact row069_identity
    · exact row070_identity
    · exact row071_identity
    · exact row072_identity
    · exact row073_identity
    · exact row074_identity
    · exact row075_identity
    · exact row076_identity
    · exact row077_identity
    · exact row078_identity
    · exact row079_identity
    · exact row080_identity
    · exact row081_identity
    · exact row082_identity
    · exact row083_identity
    · exact row084_identity
    · exact row085_identity
    · exact row086_identity
    · exact row087_identity
    · exact row088_identity
    · exact row089_identity
    · exact row090_identity
    · exact row091_identity
    · exact row092_identity
    · exact row093_identity
    · exact row094_identity
    · exact row095_identity
    · exact row096_identity
    · exact row097_identity
    · exact row098_identity
    · exact row099_identity
    · exact row100_identity
    · exact row101_identity
    · exact row102_identity
    · exact row103_identity
    · exact row104_identity
    · exact row105_identity
    · exact row106_identity
    · exact row107_identity
    · exact row108_identity
    · exact row109_identity
    · exact row110_identity
    · exact row111_identity
    · exact row112_identity
    · exact row113_identity
    · exact row114_identity
    · exact row115_identity
    · exact row116_identity
    · exact row117_identity
  · intro j
    fin_cases j
    · exact row000_nonnegative
    · exact row001_nonnegative
    · exact row002_nonnegative
    · exact row003_nonnegative
    · exact row004_nonnegative
    · exact row005_nonnegative
    · exact row006_nonnegative
    · exact row007_nonnegative
    · exact row008_nonnegative
    · exact row009_nonnegative
    · exact row010_nonnegative
    · exact row011_nonnegative
    · exact row012_nonnegative
    · exact row013_nonnegative
    · exact row014_nonnegative
    · exact row015_nonnegative
    · exact row016_nonnegative
    · exact row017_nonnegative
    · exact row018_nonnegative
    · exact row019_nonnegative
    · exact row020_nonnegative
    · exact row021_nonnegative
    · exact row022_nonnegative
    · exact row023_nonnegative
    · exact row024_nonnegative
    · exact row025_nonnegative
    · exact row026_nonnegative
    · exact row027_nonnegative
    · exact row028_nonnegative
    · exact row029_nonnegative
    · exact row030_nonnegative
    · exact row031_nonnegative
    · exact row032_nonnegative
    · exact row033_nonnegative
    · exact row034_nonnegative
    · exact row035_nonnegative
    · exact row036_nonnegative
    · exact row037_nonnegative
    · exact row038_nonnegative
    · exact row039_nonnegative
    · exact row040_nonnegative
    · exact row041_nonnegative
    · exact row042_nonnegative
    · exact row043_nonnegative
    · exact row044_nonnegative
    · exact row045_nonnegative
    · exact row046_nonnegative
    · exact row047_nonnegative
    · exact row048_nonnegative
    · exact row049_nonnegative
    · exact row050_nonnegative
    · exact row051_nonnegative
    · exact row052_nonnegative
    · exact row053_nonnegative
    · exact row054_nonnegative
    · exact row055_nonnegative
    · exact row056_nonnegative
    · exact row057_nonnegative
    · exact row058_nonnegative
    · exact row059_nonnegative
    · exact row060_nonnegative
    · exact row061_nonnegative
    · exact row062_nonnegative
    · exact row063_nonnegative
    · exact row064_nonnegative
    · exact row065_nonnegative
    · exact row066_nonnegative
    · exact row067_nonnegative
    · exact row068_nonnegative
    · exact row069_nonnegative
    · exact row070_nonnegative
    · exact row071_nonnegative
    · exact row072_nonnegative
    · exact row073_nonnegative
    · exact row074_nonnegative
    · exact row075_nonnegative
    · exact row076_nonnegative
    · exact row077_nonnegative
    · exact row078_nonnegative
    · exact row079_nonnegative
    · exact row080_nonnegative
    · exact row081_nonnegative
    · exact row082_nonnegative
    · exact row083_nonnegative
    · exact row084_nonnegative
    · exact row085_nonnegative
    · exact row086_nonnegative
    · exact row087_nonnegative
    · exact row088_nonnegative
    · exact row089_nonnegative
    · exact row090_nonnegative
    · exact row091_nonnegative
    · exact row092_nonnegative
    · exact row093_nonnegative
    · exact row094_nonnegative
    · exact row095_nonnegative
    · exact row096_nonnegative
    · exact row097_nonnegative
    · exact row098_nonnegative
    · exact row099_nonnegative
    · exact row100_nonnegative
    · exact row101_nonnegative
    · exact row102_nonnegative
    · exact row103_nonnegative
    · exact row104_nonnegative
    · exact row105_nonnegative
    · exact row106_nonnegative
    · exact row107_nonnegative
    · exact row108_nonnegative
    · exact row109_nonnegative
    · exact row110_nonnegative
    · exact row111_nonnegative
    · exact row112_nonnegative
    · exact row113_nonnegative
    · exact row114_nonnegative
    · exact row115_nonnegative
    · exact row116_nonnegative
    · exact row117_nonnegative
#print axioms weighted_margin_sign
end Gebendorfer.RadenkovicGutman.WeightedScalarMarginAnchor005Cell008
