/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm10
import Proofs.RadenkovicGutmanIntegerBernsteinWeights52
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf00447_w_raw : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1323388240920576000000000000 1430674839274636897603139871 283395917743626718726562500000))
theorem leaf00447_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack true 1323388240920576000000000000 1430674839274636897603139871 283395917743626718726562500000 leaf00447_w_raw=true := by decide +kernel
theorem leaf00447_rectangular : NestedInteger.rectangular 3 ![52,0,4] leaf00447_w_raw=true := by decide +kernel
#print axioms leaf00447_raw
#print axioms leaf00447_rectangular
def leaf00447_w_inner : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerAffineStages.inner leaf00447_w_raw ![14,0,0] ![1,1,1] ![64,1,2])
theorem leaf00447_inner : leaf00447_w_inner=IntegerAffineStages.inner leaf00447_w_raw ![14,0,0] ![1,1,1] ![64,1,2] := by decide +kernel
#print axioms leaf00447_inner
def leaf00447_w_source00 : NestedInteger.Poly 3 := leaf00447_w_inner
def leaf00447_w_segment00 : NestedInteger.Poly 3 := leaf00447_w_source00.take 12
def leaf00447_w_weights00 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 14 1 64 0 leaf00447_w_segment00)
theorem leaf00447_w_weights00_identity : leaf00447_w_weights00=IntegerWeightedOuter.weights 14 1 64 0 leaf00447_w_segment00 := by decide +kernel
def leaf00447_w_piece00 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf00447_w_weights00 leaf00447_w_segment00)
theorem leaf00447_w_piece00_weighted : leaf00447_w_piece00=IntegerWeightedOuter.applyWeights leaf00447_w_weights00 leaf00447_w_segment00 := by decide +kernel
theorem leaf00447_w_piece00_identity : leaf00447_w_piece00=IntegerOuterTerms.transform 14 1 64 0 leaf00447_w_segment00 :=
  IntegerWeightedOuter.checked 14 1 64 0 leaf00447_w_segment00 leaf00447_w_piece00 leaf00447_w_weights00 leaf00447_w_weights00_identity leaf00447_w_piece00_weighted
#print axioms leaf00447_w_weights00_identity
#print axioms leaf00447_w_piece00_weighted
#print axioms leaf00447_w_piece00_identity
def leaf00447_w_source01 : NestedInteger.Poly 3 := leaf00447_w_source00.drop 12
def leaf00447_w_segment01 : NestedInteger.Poly 3 := leaf00447_w_source01.take 12
def leaf00447_w_weights01 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 14 1 64 12 leaf00447_w_segment01)
theorem leaf00447_w_weights01_identity : leaf00447_w_weights01=IntegerWeightedOuter.weights 14 1 64 12 leaf00447_w_segment01 := by decide +kernel
def leaf00447_w_piece01 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf00447_w_weights01 leaf00447_w_segment01)
theorem leaf00447_w_piece01_weighted : leaf00447_w_piece01=IntegerWeightedOuter.applyWeights leaf00447_w_weights01 leaf00447_w_segment01 := by decide +kernel
theorem leaf00447_w_piece01_identity : leaf00447_w_piece01=IntegerOuterTerms.transform 14 1 64 12 leaf00447_w_segment01 :=
  IntegerWeightedOuter.checked 14 1 64 12 leaf00447_w_segment01 leaf00447_w_piece01 leaf00447_w_weights01 leaf00447_w_weights01_identity leaf00447_w_piece01_weighted
#print axioms leaf00447_w_weights01_identity
#print axioms leaf00447_w_piece01_weighted
#print axioms leaf00447_w_piece01_identity
def leaf00447_w_source02 : NestedInteger.Poly 3 := leaf00447_w_source01.drop 12
def leaf00447_w_segment02 : NestedInteger.Poly 3 := leaf00447_w_source02.take 12
def leaf00447_w_weights02 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 14 1 64 24 leaf00447_w_segment02)
theorem leaf00447_w_weights02_identity : leaf00447_w_weights02=IntegerWeightedOuter.weights 14 1 64 24 leaf00447_w_segment02 := by decide +kernel
def leaf00447_w_piece02 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf00447_w_weights02 leaf00447_w_segment02)
theorem leaf00447_w_piece02_weighted : leaf00447_w_piece02=IntegerWeightedOuter.applyWeights leaf00447_w_weights02 leaf00447_w_segment02 := by decide +kernel
theorem leaf00447_w_piece02_identity : leaf00447_w_piece02=IntegerOuterTerms.transform 14 1 64 24 leaf00447_w_segment02 :=
  IntegerWeightedOuter.checked 14 1 64 24 leaf00447_w_segment02 leaf00447_w_piece02 leaf00447_w_weights02 leaf00447_w_weights02_identity leaf00447_w_piece02_weighted
#print axioms leaf00447_w_weights02_identity
#print axioms leaf00447_w_piece02_weighted
#print axioms leaf00447_w_piece02_identity
def leaf00447_w_source03 : NestedInteger.Poly 3 := leaf00447_w_source02.drop 12
def leaf00447_w_segment03 : NestedInteger.Poly 3 := leaf00447_w_source03.take 12
def leaf00447_w_weights03 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 14 1 64 36 leaf00447_w_segment03)
theorem leaf00447_w_weights03_identity : leaf00447_w_weights03=IntegerWeightedOuter.weights 14 1 64 36 leaf00447_w_segment03 := by decide +kernel
def leaf00447_w_piece03 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf00447_w_weights03 leaf00447_w_segment03)
theorem leaf00447_w_piece03_weighted : leaf00447_w_piece03=IntegerWeightedOuter.applyWeights leaf00447_w_weights03 leaf00447_w_segment03 := by decide +kernel
theorem leaf00447_w_piece03_identity : leaf00447_w_piece03=IntegerOuterTerms.transform 14 1 64 36 leaf00447_w_segment03 :=
  IntegerWeightedOuter.checked 14 1 64 36 leaf00447_w_segment03 leaf00447_w_piece03 leaf00447_w_weights03 leaf00447_w_weights03_identity leaf00447_w_piece03_weighted
#print axioms leaf00447_w_weights03_identity
#print axioms leaf00447_w_piece03_weighted
#print axioms leaf00447_w_piece03_identity
def leaf00447_w_source04 : NestedInteger.Poly 3 := leaf00447_w_source03.drop 12
def leaf00447_w_segment04 : NestedInteger.Poly 3 := leaf00447_w_source04.take 12
def leaf00447_w_weights04 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 14 1 64 48 leaf00447_w_segment04)
theorem leaf00447_w_weights04_identity : leaf00447_w_weights04=IntegerWeightedOuter.weights 14 1 64 48 leaf00447_w_segment04 := by decide +kernel
def leaf00447_w_piece04 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf00447_w_weights04 leaf00447_w_segment04)
theorem leaf00447_w_piece04_weighted : leaf00447_w_piece04=IntegerWeightedOuter.applyWeights leaf00447_w_weights04 leaf00447_w_segment04 := by decide +kernel
theorem leaf00447_w_piece04_identity : leaf00447_w_piece04=IntegerOuterTerms.transform 14 1 64 48 leaf00447_w_segment04 :=
  IntegerWeightedOuter.checked 14 1 64 48 leaf00447_w_segment04 leaf00447_w_piece04 leaf00447_w_weights04 leaf00447_w_weights04_identity leaf00447_w_piece04_weighted
#print axioms leaf00447_w_weights04_identity
#print axioms leaf00447_w_piece04_weighted
#print axioms leaf00447_w_piece04_identity
def leaf00447_w_suffix04 : NestedInteger.Poly 3 := leaf00447_w_piece04
theorem leaf00447_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00447_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 48 leaf00447_w_source04)) x := by
  have h : leaf00447_w_segment04=leaf00447_w_source04 := by decide +kernel
  rw [leaf00447_w_suffix04,leaf00447_w_piece04_identity,h]
#print axioms leaf00447_w_suffix04_eval
def leaf00447_w_suffix03 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source04.length) leaf00447_w_piece03) leaf00447_w_suffix04)
theorem leaf00447_w_suffix03_join : leaf00447_w_suffix03=NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source04.length) leaf00447_w_piece03) leaf00447_w_suffix04 := by decide +kernel
theorem leaf00447_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00447_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 36 leaf00447_w_source03)) x := by
  have hlen : leaf00447_w_segment03.length=12 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf00447_w_source04.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 36 leaf00447_w_segment03)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 (36+leaf00447_w_segment03.length) leaf00447_w_source04)) x := by
      rw [leaf00447_w_suffix03_join,cast_add,eval_add,cast_scale,eval_scale,leaf00447_w_piece03_identity,leaf00447_w_suffix04_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 36 (leaf00447_w_segment03++leaf00447_w_source04))) x :=
      (IntegerOuterPieces.eval_append 14 1 64 36 leaf00447_w_segment03 leaf00447_w_source04 x).symm
    _ = _ := by rw [show leaf00447_w_segment03++leaf00447_w_source04=leaf00447_w_source03 from List.take_append_drop 12 leaf00447_w_source03]
#print axioms leaf00447_w_suffix03_join
#print axioms leaf00447_w_suffix03_eval
def leaf00447_w_suffix02 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source03.length) leaf00447_w_piece02) leaf00447_w_suffix03)
theorem leaf00447_w_suffix02_join : leaf00447_w_suffix02=NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source03.length) leaf00447_w_piece02) leaf00447_w_suffix03 := by decide +kernel
theorem leaf00447_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00447_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 24 leaf00447_w_source02)) x := by
  have hlen : leaf00447_w_segment02.length=12 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf00447_w_source03.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 24 leaf00447_w_segment02)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 (24+leaf00447_w_segment02.length) leaf00447_w_source03)) x := by
      rw [leaf00447_w_suffix02_join,cast_add,eval_add,cast_scale,eval_scale,leaf00447_w_piece02_identity,leaf00447_w_suffix03_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 24 (leaf00447_w_segment02++leaf00447_w_source03))) x :=
      (IntegerOuterPieces.eval_append 14 1 64 24 leaf00447_w_segment02 leaf00447_w_source03 x).symm
    _ = _ := by rw [show leaf00447_w_segment02++leaf00447_w_source03=leaf00447_w_source02 from List.take_append_drop 12 leaf00447_w_source02]
#print axioms leaf00447_w_suffix02_join
#print axioms leaf00447_w_suffix02_eval
def leaf00447_w_suffix01 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source02.length) leaf00447_w_piece01) leaf00447_w_suffix02)
theorem leaf00447_w_suffix01_join : leaf00447_w_suffix01=NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source02.length) leaf00447_w_piece01) leaf00447_w_suffix02 := by decide +kernel
theorem leaf00447_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00447_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 12 leaf00447_w_source01)) x := by
  have hlen : leaf00447_w_segment01.length=12 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf00447_w_source02.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 12 leaf00447_w_segment01)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 (12+leaf00447_w_segment01.length) leaf00447_w_source02)) x := by
      rw [leaf00447_w_suffix01_join,cast_add,eval_add,cast_scale,eval_scale,leaf00447_w_piece01_identity,leaf00447_w_suffix02_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 12 (leaf00447_w_segment01++leaf00447_w_source02))) x :=
      (IntegerOuterPieces.eval_append 14 1 64 12 leaf00447_w_segment01 leaf00447_w_source02 x).symm
    _ = _ := by rw [show leaf00447_w_segment01++leaf00447_w_source02=leaf00447_w_source01 from List.take_append_drop 12 leaf00447_w_source01]
#print axioms leaf00447_w_suffix01_join
#print axioms leaf00447_w_suffix01_eval
def leaf00447_w_affine : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source01.length) leaf00447_w_piece00) leaf00447_w_suffix01)
theorem leaf00447_w_affine_join : leaf00447_w_affine=NestedInteger.add (NestedInteger.scale (64^leaf00447_w_source01.length) leaf00447_w_piece00) leaf00447_w_suffix01 := by decide +kernel
theorem leaf00447_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf00447_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 0 leaf00447_w_source00)) x := by
  have hlen : leaf00447_w_segment00.length=12 := by decide +kernel
  calc
    _ = (64 : ℝ)^leaf00447_w_source01.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 0 leaf00447_w_segment00)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 (0+leaf00447_w_segment00.length) leaf00447_w_source01)) x := by
      rw [leaf00447_w_affine_join,cast_add,eval_add,cast_scale,eval_scale,leaf00447_w_piece00_identity,leaf00447_w_suffix01_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 14 1 64 0 (leaf00447_w_segment00++leaf00447_w_source01))) x :=
      (IntegerOuterPieces.eval_append 14 1 64 0 leaf00447_w_segment00 leaf00447_w_source01 x).symm
    _ = _ := by rw [show leaf00447_w_segment00++leaf00447_w_source01=leaf00447_w_source00 from List.take_append_drop 12 leaf00447_w_source00]
#print axioms leaf00447_w_affine_join
#print axioms leaf00447_w_affine_eval
theorem leaf00447_w_affine_length : leaf00447_w_affine.length=53 := by decide +kernel
#print axioms leaf00447_w_affine_length
def leaf00447_w_row000 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row000 leaf00447_w_affine)
theorem leaf00447_w_row000_weighted : leaf00447_w_row000=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row000 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row000_identity : leaf00447_w_row000=NestedInteger.coefficientFrom 52 0 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 0 0 leaf00447_w_affine leaf00447_w_row000 IntegerBernsteinWeights52.row000 (IntegerBernsteinTable.checked (n := 2) 52 0 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row000 leaf00447_w_affine_length IntegerBernsteinWeights52.row000_identity) leaf00447_w_row000_weighted
theorem leaf00447_w_row000_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row000=true := by decide +kernel
#print axioms leaf00447_w_row000_weighted
#print axioms leaf00447_w_row000_identity
#print axioms leaf00447_w_row000_positive
def leaf00447_w_row001 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row001 leaf00447_w_affine)
theorem leaf00447_w_row001_weighted : leaf00447_w_row001=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row001 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row001_identity : leaf00447_w_row001=NestedInteger.coefficientFrom 52 1 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 1 0 leaf00447_w_affine leaf00447_w_row001 IntegerBernsteinWeights52.row001 (IntegerBernsteinTable.checked (n := 2) 52 1 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row001 leaf00447_w_affine_length IntegerBernsteinWeights52.row001_identity) leaf00447_w_row001_weighted
theorem leaf00447_w_row001_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row001=true := by decide +kernel
#print axioms leaf00447_w_row001_weighted
#print axioms leaf00447_w_row001_identity
#print axioms leaf00447_w_row001_positive
def leaf00447_w_row002 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row002 leaf00447_w_affine)
theorem leaf00447_w_row002_weighted : leaf00447_w_row002=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row002 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row002_identity : leaf00447_w_row002=NestedInteger.coefficientFrom 52 2 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 2 0 leaf00447_w_affine leaf00447_w_row002 IntegerBernsteinWeights52.row002 (IntegerBernsteinTable.checked (n := 2) 52 2 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row002 leaf00447_w_affine_length IntegerBernsteinWeights52.row002_identity) leaf00447_w_row002_weighted
theorem leaf00447_w_row002_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row002=true := by decide +kernel
#print axioms leaf00447_w_row002_weighted
#print axioms leaf00447_w_row002_identity
#print axioms leaf00447_w_row002_positive
def leaf00447_w_row003 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row003 leaf00447_w_affine)
theorem leaf00447_w_row003_weighted : leaf00447_w_row003=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row003 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row003_identity : leaf00447_w_row003=NestedInteger.coefficientFrom 52 3 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 3 0 leaf00447_w_affine leaf00447_w_row003 IntegerBernsteinWeights52.row003 (IntegerBernsteinTable.checked (n := 2) 52 3 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row003 leaf00447_w_affine_length IntegerBernsteinWeights52.row003_identity) leaf00447_w_row003_weighted
theorem leaf00447_w_row003_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row003=true := by decide +kernel
#print axioms leaf00447_w_row003_weighted
#print axioms leaf00447_w_row003_identity
#print axioms leaf00447_w_row003_positive
def leaf00447_w_row004 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row004 leaf00447_w_affine)
theorem leaf00447_w_row004_weighted : leaf00447_w_row004=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row004 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row004_identity : leaf00447_w_row004=NestedInteger.coefficientFrom 52 4 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 4 0 leaf00447_w_affine leaf00447_w_row004 IntegerBernsteinWeights52.row004 (IntegerBernsteinTable.checked (n := 2) 52 4 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row004 leaf00447_w_affine_length IntegerBernsteinWeights52.row004_identity) leaf00447_w_row004_weighted
theorem leaf00447_w_row004_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row004=true := by decide +kernel
#print axioms leaf00447_w_row004_weighted
#print axioms leaf00447_w_row004_identity
#print axioms leaf00447_w_row004_positive
def leaf00447_w_row005 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row005 leaf00447_w_affine)
theorem leaf00447_w_row005_weighted : leaf00447_w_row005=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row005 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row005_identity : leaf00447_w_row005=NestedInteger.coefficientFrom 52 5 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 5 0 leaf00447_w_affine leaf00447_w_row005 IntegerBernsteinWeights52.row005 (IntegerBernsteinTable.checked (n := 2) 52 5 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row005 leaf00447_w_affine_length IntegerBernsteinWeights52.row005_identity) leaf00447_w_row005_weighted
theorem leaf00447_w_row005_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row005=true := by decide +kernel
#print axioms leaf00447_w_row005_weighted
#print axioms leaf00447_w_row005_identity
#print axioms leaf00447_w_row005_positive
def leaf00447_w_row006 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row006 leaf00447_w_affine)
theorem leaf00447_w_row006_weighted : leaf00447_w_row006=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row006 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row006_identity : leaf00447_w_row006=NestedInteger.coefficientFrom 52 6 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 6 0 leaf00447_w_affine leaf00447_w_row006 IntegerBernsteinWeights52.row006 (IntegerBernsteinTable.checked (n := 2) 52 6 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row006 leaf00447_w_affine_length IntegerBernsteinWeights52.row006_identity) leaf00447_w_row006_weighted
theorem leaf00447_w_row006_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row006=true := by decide +kernel
#print axioms leaf00447_w_row006_weighted
#print axioms leaf00447_w_row006_identity
#print axioms leaf00447_w_row006_positive
def leaf00447_w_row007 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row007 leaf00447_w_affine)
theorem leaf00447_w_row007_weighted : leaf00447_w_row007=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row007 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row007_identity : leaf00447_w_row007=NestedInteger.coefficientFrom 52 7 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 7 0 leaf00447_w_affine leaf00447_w_row007 IntegerBernsteinWeights52.row007 (IntegerBernsteinTable.checked (n := 2) 52 7 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row007 leaf00447_w_affine_length IntegerBernsteinWeights52.row007_identity) leaf00447_w_row007_weighted
theorem leaf00447_w_row007_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row007=true := by decide +kernel
#print axioms leaf00447_w_row007_weighted
#print axioms leaf00447_w_row007_identity
#print axioms leaf00447_w_row007_positive
def leaf00447_w_row008 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row008 leaf00447_w_affine)
theorem leaf00447_w_row008_weighted : leaf00447_w_row008=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row008 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row008_identity : leaf00447_w_row008=NestedInteger.coefficientFrom 52 8 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 8 0 leaf00447_w_affine leaf00447_w_row008 IntegerBernsteinWeights52.row008 (IntegerBernsteinTable.checked (n := 2) 52 8 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row008 leaf00447_w_affine_length IntegerBernsteinWeights52.row008_identity) leaf00447_w_row008_weighted
theorem leaf00447_w_row008_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row008=true := by decide +kernel
#print axioms leaf00447_w_row008_weighted
#print axioms leaf00447_w_row008_identity
#print axioms leaf00447_w_row008_positive
def leaf00447_w_row009 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row009 leaf00447_w_affine)
theorem leaf00447_w_row009_weighted : leaf00447_w_row009=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row009 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row009_identity : leaf00447_w_row009=NestedInteger.coefficientFrom 52 9 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 9 0 leaf00447_w_affine leaf00447_w_row009 IntegerBernsteinWeights52.row009 (IntegerBernsteinTable.checked (n := 2) 52 9 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row009 leaf00447_w_affine_length IntegerBernsteinWeights52.row009_identity) leaf00447_w_row009_weighted
theorem leaf00447_w_row009_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row009=true := by decide +kernel
#print axioms leaf00447_w_row009_weighted
#print axioms leaf00447_w_row009_identity
#print axioms leaf00447_w_row009_positive
def leaf00447_w_row010 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row010 leaf00447_w_affine)
theorem leaf00447_w_row010_weighted : leaf00447_w_row010=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row010 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row010_identity : leaf00447_w_row010=NestedInteger.coefficientFrom 52 10 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 10 0 leaf00447_w_affine leaf00447_w_row010 IntegerBernsteinWeights52.row010 (IntegerBernsteinTable.checked (n := 2) 52 10 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row010 leaf00447_w_affine_length IntegerBernsteinWeights52.row010_identity) leaf00447_w_row010_weighted
theorem leaf00447_w_row010_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row010=true := by decide +kernel
#print axioms leaf00447_w_row010_weighted
#print axioms leaf00447_w_row010_identity
#print axioms leaf00447_w_row010_positive
def leaf00447_w_row011 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row011 leaf00447_w_affine)
theorem leaf00447_w_row011_weighted : leaf00447_w_row011=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row011 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row011_identity : leaf00447_w_row011=NestedInteger.coefficientFrom 52 11 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 11 0 leaf00447_w_affine leaf00447_w_row011 IntegerBernsteinWeights52.row011 (IntegerBernsteinTable.checked (n := 2) 52 11 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row011 leaf00447_w_affine_length IntegerBernsteinWeights52.row011_identity) leaf00447_w_row011_weighted
theorem leaf00447_w_row011_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row011=true := by decide +kernel
#print axioms leaf00447_w_row011_weighted
#print axioms leaf00447_w_row011_identity
#print axioms leaf00447_w_row011_positive
def leaf00447_w_row012 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row012 leaf00447_w_affine)
theorem leaf00447_w_row012_weighted : leaf00447_w_row012=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row012 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row012_identity : leaf00447_w_row012=NestedInteger.coefficientFrom 52 12 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 12 0 leaf00447_w_affine leaf00447_w_row012 IntegerBernsteinWeights52.row012 (IntegerBernsteinTable.checked (n := 2) 52 12 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row012 leaf00447_w_affine_length IntegerBernsteinWeights52.row012_identity) leaf00447_w_row012_weighted
theorem leaf00447_w_row012_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row012=true := by decide +kernel
#print axioms leaf00447_w_row012_weighted
#print axioms leaf00447_w_row012_identity
#print axioms leaf00447_w_row012_positive
def leaf00447_w_row013 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row013 leaf00447_w_affine)
theorem leaf00447_w_row013_weighted : leaf00447_w_row013=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row013 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row013_identity : leaf00447_w_row013=NestedInteger.coefficientFrom 52 13 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 13 0 leaf00447_w_affine leaf00447_w_row013 IntegerBernsteinWeights52.row013 (IntegerBernsteinTable.checked (n := 2) 52 13 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row013 leaf00447_w_affine_length IntegerBernsteinWeights52.row013_identity) leaf00447_w_row013_weighted
theorem leaf00447_w_row013_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row013=true := by decide +kernel
#print axioms leaf00447_w_row013_weighted
#print axioms leaf00447_w_row013_identity
#print axioms leaf00447_w_row013_positive
def leaf00447_w_row014 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row014 leaf00447_w_affine)
theorem leaf00447_w_row014_weighted : leaf00447_w_row014=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row014 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row014_identity : leaf00447_w_row014=NestedInteger.coefficientFrom 52 14 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 14 0 leaf00447_w_affine leaf00447_w_row014 IntegerBernsteinWeights52.row014 (IntegerBernsteinTable.checked (n := 2) 52 14 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row014 leaf00447_w_affine_length IntegerBernsteinWeights52.row014_identity) leaf00447_w_row014_weighted
theorem leaf00447_w_row014_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row014=true := by decide +kernel
#print axioms leaf00447_w_row014_weighted
#print axioms leaf00447_w_row014_identity
#print axioms leaf00447_w_row014_positive
def leaf00447_w_row015 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row015 leaf00447_w_affine)
theorem leaf00447_w_row015_weighted : leaf00447_w_row015=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row015 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row015_identity : leaf00447_w_row015=NestedInteger.coefficientFrom 52 15 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 15 0 leaf00447_w_affine leaf00447_w_row015 IntegerBernsteinWeights52.row015 (IntegerBernsteinTable.checked (n := 2) 52 15 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row015 leaf00447_w_affine_length IntegerBernsteinWeights52.row015_identity) leaf00447_w_row015_weighted
theorem leaf00447_w_row015_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row015=true := by decide +kernel
#print axioms leaf00447_w_row015_weighted
#print axioms leaf00447_w_row015_identity
#print axioms leaf00447_w_row015_positive
def leaf00447_w_row016 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row016 leaf00447_w_affine)
theorem leaf00447_w_row016_weighted : leaf00447_w_row016=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row016 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row016_identity : leaf00447_w_row016=NestedInteger.coefficientFrom 52 16 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 16 0 leaf00447_w_affine leaf00447_w_row016 IntegerBernsteinWeights52.row016 (IntegerBernsteinTable.checked (n := 2) 52 16 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row016 leaf00447_w_affine_length IntegerBernsteinWeights52.row016_identity) leaf00447_w_row016_weighted
theorem leaf00447_w_row016_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row016=true := by decide +kernel
#print axioms leaf00447_w_row016_weighted
#print axioms leaf00447_w_row016_identity
#print axioms leaf00447_w_row016_positive
def leaf00447_w_row017 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row017 leaf00447_w_affine)
theorem leaf00447_w_row017_weighted : leaf00447_w_row017=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row017 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row017_identity : leaf00447_w_row017=NestedInteger.coefficientFrom 52 17 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 17 0 leaf00447_w_affine leaf00447_w_row017 IntegerBernsteinWeights52.row017 (IntegerBernsteinTable.checked (n := 2) 52 17 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row017 leaf00447_w_affine_length IntegerBernsteinWeights52.row017_identity) leaf00447_w_row017_weighted
theorem leaf00447_w_row017_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row017=true := by decide +kernel
#print axioms leaf00447_w_row017_weighted
#print axioms leaf00447_w_row017_identity
#print axioms leaf00447_w_row017_positive
def leaf00447_w_row018 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row018 leaf00447_w_affine)
theorem leaf00447_w_row018_weighted : leaf00447_w_row018=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row018 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row018_identity : leaf00447_w_row018=NestedInteger.coefficientFrom 52 18 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 18 0 leaf00447_w_affine leaf00447_w_row018 IntegerBernsteinWeights52.row018 (IntegerBernsteinTable.checked (n := 2) 52 18 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row018 leaf00447_w_affine_length IntegerBernsteinWeights52.row018_identity) leaf00447_w_row018_weighted
theorem leaf00447_w_row018_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row018=true := by decide +kernel
#print axioms leaf00447_w_row018_weighted
#print axioms leaf00447_w_row018_identity
#print axioms leaf00447_w_row018_positive
def leaf00447_w_row019 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row019 leaf00447_w_affine)
theorem leaf00447_w_row019_weighted : leaf00447_w_row019=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row019 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row019_identity : leaf00447_w_row019=NestedInteger.coefficientFrom 52 19 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 19 0 leaf00447_w_affine leaf00447_w_row019 IntegerBernsteinWeights52.row019 (IntegerBernsteinTable.checked (n := 2) 52 19 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row019 leaf00447_w_affine_length IntegerBernsteinWeights52.row019_identity) leaf00447_w_row019_weighted
theorem leaf00447_w_row019_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row019=true := by decide +kernel
#print axioms leaf00447_w_row019_weighted
#print axioms leaf00447_w_row019_identity
#print axioms leaf00447_w_row019_positive
def leaf00447_w_row020 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row020 leaf00447_w_affine)
theorem leaf00447_w_row020_weighted : leaf00447_w_row020=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row020 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row020_identity : leaf00447_w_row020=NestedInteger.coefficientFrom 52 20 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 20 0 leaf00447_w_affine leaf00447_w_row020 IntegerBernsteinWeights52.row020 (IntegerBernsteinTable.checked (n := 2) 52 20 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row020 leaf00447_w_affine_length IntegerBernsteinWeights52.row020_identity) leaf00447_w_row020_weighted
theorem leaf00447_w_row020_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row020=true := by decide +kernel
#print axioms leaf00447_w_row020_weighted
#print axioms leaf00447_w_row020_identity
#print axioms leaf00447_w_row020_positive
def leaf00447_w_row021 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row021 leaf00447_w_affine)
theorem leaf00447_w_row021_weighted : leaf00447_w_row021=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row021 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row021_identity : leaf00447_w_row021=NestedInteger.coefficientFrom 52 21 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 21 0 leaf00447_w_affine leaf00447_w_row021 IntegerBernsteinWeights52.row021 (IntegerBernsteinTable.checked (n := 2) 52 21 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row021 leaf00447_w_affine_length IntegerBernsteinWeights52.row021_identity) leaf00447_w_row021_weighted
theorem leaf00447_w_row021_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row021=true := by decide +kernel
#print axioms leaf00447_w_row021_weighted
#print axioms leaf00447_w_row021_identity
#print axioms leaf00447_w_row021_positive
def leaf00447_w_row022 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row022 leaf00447_w_affine)
theorem leaf00447_w_row022_weighted : leaf00447_w_row022=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row022 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row022_identity : leaf00447_w_row022=NestedInteger.coefficientFrom 52 22 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 22 0 leaf00447_w_affine leaf00447_w_row022 IntegerBernsteinWeights52.row022 (IntegerBernsteinTable.checked (n := 2) 52 22 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row022 leaf00447_w_affine_length IntegerBernsteinWeights52.row022_identity) leaf00447_w_row022_weighted
theorem leaf00447_w_row022_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row022=true := by decide +kernel
#print axioms leaf00447_w_row022_weighted
#print axioms leaf00447_w_row022_identity
#print axioms leaf00447_w_row022_positive
def leaf00447_w_row023 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row023 leaf00447_w_affine)
theorem leaf00447_w_row023_weighted : leaf00447_w_row023=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row023 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row023_identity : leaf00447_w_row023=NestedInteger.coefficientFrom 52 23 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 23 0 leaf00447_w_affine leaf00447_w_row023 IntegerBernsteinWeights52.row023 (IntegerBernsteinTable.checked (n := 2) 52 23 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row023 leaf00447_w_affine_length IntegerBernsteinWeights52.row023_identity) leaf00447_w_row023_weighted
theorem leaf00447_w_row023_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row023=true := by decide +kernel
#print axioms leaf00447_w_row023_weighted
#print axioms leaf00447_w_row023_identity
#print axioms leaf00447_w_row023_positive
def leaf00447_w_row024 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row024 leaf00447_w_affine)
theorem leaf00447_w_row024_weighted : leaf00447_w_row024=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row024 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row024_identity : leaf00447_w_row024=NestedInteger.coefficientFrom 52 24 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 24 0 leaf00447_w_affine leaf00447_w_row024 IntegerBernsteinWeights52.row024 (IntegerBernsteinTable.checked (n := 2) 52 24 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row024 leaf00447_w_affine_length IntegerBernsteinWeights52.row024_identity) leaf00447_w_row024_weighted
theorem leaf00447_w_row024_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row024=true := by decide +kernel
#print axioms leaf00447_w_row024_weighted
#print axioms leaf00447_w_row024_identity
#print axioms leaf00447_w_row024_positive
def leaf00447_w_row025 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row025 leaf00447_w_affine)
theorem leaf00447_w_row025_weighted : leaf00447_w_row025=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row025 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row025_identity : leaf00447_w_row025=NestedInteger.coefficientFrom 52 25 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 25 0 leaf00447_w_affine leaf00447_w_row025 IntegerBernsteinWeights52.row025 (IntegerBernsteinTable.checked (n := 2) 52 25 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row025 leaf00447_w_affine_length IntegerBernsteinWeights52.row025_identity) leaf00447_w_row025_weighted
theorem leaf00447_w_row025_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row025=true := by decide +kernel
#print axioms leaf00447_w_row025_weighted
#print axioms leaf00447_w_row025_identity
#print axioms leaf00447_w_row025_positive
def leaf00447_w_row026 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row026 leaf00447_w_affine)
theorem leaf00447_w_row026_weighted : leaf00447_w_row026=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row026 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row026_identity : leaf00447_w_row026=NestedInteger.coefficientFrom 52 26 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 26 0 leaf00447_w_affine leaf00447_w_row026 IntegerBernsteinWeights52.row026 (IntegerBernsteinTable.checked (n := 2) 52 26 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row026 leaf00447_w_affine_length IntegerBernsteinWeights52.row026_identity) leaf00447_w_row026_weighted
theorem leaf00447_w_row026_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row026=true := by decide +kernel
#print axioms leaf00447_w_row026_weighted
#print axioms leaf00447_w_row026_identity
#print axioms leaf00447_w_row026_positive
def leaf00447_w_row027 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row027 leaf00447_w_affine)
theorem leaf00447_w_row027_weighted : leaf00447_w_row027=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row027 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row027_identity : leaf00447_w_row027=NestedInteger.coefficientFrom 52 27 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 27 0 leaf00447_w_affine leaf00447_w_row027 IntegerBernsteinWeights52.row027 (IntegerBernsteinTable.checked (n := 2) 52 27 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row027 leaf00447_w_affine_length IntegerBernsteinWeights52.row027_identity) leaf00447_w_row027_weighted
theorem leaf00447_w_row027_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row027=true := by decide +kernel
#print axioms leaf00447_w_row027_weighted
#print axioms leaf00447_w_row027_identity
#print axioms leaf00447_w_row027_positive
def leaf00447_w_row028 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row028 leaf00447_w_affine)
theorem leaf00447_w_row028_weighted : leaf00447_w_row028=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row028 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row028_identity : leaf00447_w_row028=NestedInteger.coefficientFrom 52 28 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 28 0 leaf00447_w_affine leaf00447_w_row028 IntegerBernsteinWeights52.row028 (IntegerBernsteinTable.checked (n := 2) 52 28 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row028 leaf00447_w_affine_length IntegerBernsteinWeights52.row028_identity) leaf00447_w_row028_weighted
theorem leaf00447_w_row028_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row028=true := by decide +kernel
#print axioms leaf00447_w_row028_weighted
#print axioms leaf00447_w_row028_identity
#print axioms leaf00447_w_row028_positive
def leaf00447_w_row029 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row029 leaf00447_w_affine)
theorem leaf00447_w_row029_weighted : leaf00447_w_row029=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row029 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row029_identity : leaf00447_w_row029=NestedInteger.coefficientFrom 52 29 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 29 0 leaf00447_w_affine leaf00447_w_row029 IntegerBernsteinWeights52.row029 (IntegerBernsteinTable.checked (n := 2) 52 29 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row029 leaf00447_w_affine_length IntegerBernsteinWeights52.row029_identity) leaf00447_w_row029_weighted
theorem leaf00447_w_row029_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row029=true := by decide +kernel
#print axioms leaf00447_w_row029_weighted
#print axioms leaf00447_w_row029_identity
#print axioms leaf00447_w_row029_positive
def leaf00447_w_row030 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row030 leaf00447_w_affine)
theorem leaf00447_w_row030_weighted : leaf00447_w_row030=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row030 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row030_identity : leaf00447_w_row030=NestedInteger.coefficientFrom 52 30 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 30 0 leaf00447_w_affine leaf00447_w_row030 IntegerBernsteinWeights52.row030 (IntegerBernsteinTable.checked (n := 2) 52 30 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row030 leaf00447_w_affine_length IntegerBernsteinWeights52.row030_identity) leaf00447_w_row030_weighted
theorem leaf00447_w_row030_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row030=true := by decide +kernel
#print axioms leaf00447_w_row030_weighted
#print axioms leaf00447_w_row030_identity
#print axioms leaf00447_w_row030_positive
def leaf00447_w_row031 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row031 leaf00447_w_affine)
theorem leaf00447_w_row031_weighted : leaf00447_w_row031=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row031 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row031_identity : leaf00447_w_row031=NestedInteger.coefficientFrom 52 31 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 31 0 leaf00447_w_affine leaf00447_w_row031 IntegerBernsteinWeights52.row031 (IntegerBernsteinTable.checked (n := 2) 52 31 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row031 leaf00447_w_affine_length IntegerBernsteinWeights52.row031_identity) leaf00447_w_row031_weighted
theorem leaf00447_w_row031_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row031=true := by decide +kernel
#print axioms leaf00447_w_row031_weighted
#print axioms leaf00447_w_row031_identity
#print axioms leaf00447_w_row031_positive
def leaf00447_w_row032 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row032 leaf00447_w_affine)
theorem leaf00447_w_row032_weighted : leaf00447_w_row032=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row032 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row032_identity : leaf00447_w_row032=NestedInteger.coefficientFrom 52 32 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 32 0 leaf00447_w_affine leaf00447_w_row032 IntegerBernsteinWeights52.row032 (IntegerBernsteinTable.checked (n := 2) 52 32 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row032 leaf00447_w_affine_length IntegerBernsteinWeights52.row032_identity) leaf00447_w_row032_weighted
theorem leaf00447_w_row032_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row032=true := by decide +kernel
#print axioms leaf00447_w_row032_weighted
#print axioms leaf00447_w_row032_identity
#print axioms leaf00447_w_row032_positive
def leaf00447_w_row033 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row033 leaf00447_w_affine)
theorem leaf00447_w_row033_weighted : leaf00447_w_row033=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row033 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row033_identity : leaf00447_w_row033=NestedInteger.coefficientFrom 52 33 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 33 0 leaf00447_w_affine leaf00447_w_row033 IntegerBernsteinWeights52.row033 (IntegerBernsteinTable.checked (n := 2) 52 33 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row033 leaf00447_w_affine_length IntegerBernsteinWeights52.row033_identity) leaf00447_w_row033_weighted
theorem leaf00447_w_row033_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row033=true := by decide +kernel
#print axioms leaf00447_w_row033_weighted
#print axioms leaf00447_w_row033_identity
#print axioms leaf00447_w_row033_positive
def leaf00447_w_row034 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row034 leaf00447_w_affine)
theorem leaf00447_w_row034_weighted : leaf00447_w_row034=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row034 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row034_identity : leaf00447_w_row034=NestedInteger.coefficientFrom 52 34 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 34 0 leaf00447_w_affine leaf00447_w_row034 IntegerBernsteinWeights52.row034 (IntegerBernsteinTable.checked (n := 2) 52 34 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row034 leaf00447_w_affine_length IntegerBernsteinWeights52.row034_identity) leaf00447_w_row034_weighted
theorem leaf00447_w_row034_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row034=true := by decide +kernel
#print axioms leaf00447_w_row034_weighted
#print axioms leaf00447_w_row034_identity
#print axioms leaf00447_w_row034_positive
def leaf00447_w_row035 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row035 leaf00447_w_affine)
theorem leaf00447_w_row035_weighted : leaf00447_w_row035=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row035 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row035_identity : leaf00447_w_row035=NestedInteger.coefficientFrom 52 35 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 35 0 leaf00447_w_affine leaf00447_w_row035 IntegerBernsteinWeights52.row035 (IntegerBernsteinTable.checked (n := 2) 52 35 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row035 leaf00447_w_affine_length IntegerBernsteinWeights52.row035_identity) leaf00447_w_row035_weighted
theorem leaf00447_w_row035_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row035=true := by decide +kernel
#print axioms leaf00447_w_row035_weighted
#print axioms leaf00447_w_row035_identity
#print axioms leaf00447_w_row035_positive
def leaf00447_w_row036 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row036 leaf00447_w_affine)
theorem leaf00447_w_row036_weighted : leaf00447_w_row036=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row036 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row036_identity : leaf00447_w_row036=NestedInteger.coefficientFrom 52 36 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 36 0 leaf00447_w_affine leaf00447_w_row036 IntegerBernsteinWeights52.row036 (IntegerBernsteinTable.checked (n := 2) 52 36 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row036 leaf00447_w_affine_length IntegerBernsteinWeights52.row036_identity) leaf00447_w_row036_weighted
theorem leaf00447_w_row036_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row036=true := by decide +kernel
#print axioms leaf00447_w_row036_weighted
#print axioms leaf00447_w_row036_identity
#print axioms leaf00447_w_row036_positive
def leaf00447_w_row037 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row037 leaf00447_w_affine)
theorem leaf00447_w_row037_weighted : leaf00447_w_row037=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row037 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row037_identity : leaf00447_w_row037=NestedInteger.coefficientFrom 52 37 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 37 0 leaf00447_w_affine leaf00447_w_row037 IntegerBernsteinWeights52.row037 (IntegerBernsteinTable.checked (n := 2) 52 37 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row037 leaf00447_w_affine_length IntegerBernsteinWeights52.row037_identity) leaf00447_w_row037_weighted
theorem leaf00447_w_row037_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row037=true := by decide +kernel
#print axioms leaf00447_w_row037_weighted
#print axioms leaf00447_w_row037_identity
#print axioms leaf00447_w_row037_positive
def leaf00447_w_row038 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row038 leaf00447_w_affine)
theorem leaf00447_w_row038_weighted : leaf00447_w_row038=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row038 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row038_identity : leaf00447_w_row038=NestedInteger.coefficientFrom 52 38 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 38 0 leaf00447_w_affine leaf00447_w_row038 IntegerBernsteinWeights52.row038 (IntegerBernsteinTable.checked (n := 2) 52 38 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row038 leaf00447_w_affine_length IntegerBernsteinWeights52.row038_identity) leaf00447_w_row038_weighted
theorem leaf00447_w_row038_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row038=true := by decide +kernel
#print axioms leaf00447_w_row038_weighted
#print axioms leaf00447_w_row038_identity
#print axioms leaf00447_w_row038_positive
def leaf00447_w_row039 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row039 leaf00447_w_affine)
theorem leaf00447_w_row039_weighted : leaf00447_w_row039=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row039 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row039_identity : leaf00447_w_row039=NestedInteger.coefficientFrom 52 39 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 39 0 leaf00447_w_affine leaf00447_w_row039 IntegerBernsteinWeights52.row039 (IntegerBernsteinTable.checked (n := 2) 52 39 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row039 leaf00447_w_affine_length IntegerBernsteinWeights52.row039_identity) leaf00447_w_row039_weighted
theorem leaf00447_w_row039_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row039=true := by decide +kernel
#print axioms leaf00447_w_row039_weighted
#print axioms leaf00447_w_row039_identity
#print axioms leaf00447_w_row039_positive
def leaf00447_w_row040 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row040 leaf00447_w_affine)
theorem leaf00447_w_row040_weighted : leaf00447_w_row040=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row040 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row040_identity : leaf00447_w_row040=NestedInteger.coefficientFrom 52 40 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 40 0 leaf00447_w_affine leaf00447_w_row040 IntegerBernsteinWeights52.row040 (IntegerBernsteinTable.checked (n := 2) 52 40 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row040 leaf00447_w_affine_length IntegerBernsteinWeights52.row040_identity) leaf00447_w_row040_weighted
theorem leaf00447_w_row040_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row040=true := by decide +kernel
#print axioms leaf00447_w_row040_weighted
#print axioms leaf00447_w_row040_identity
#print axioms leaf00447_w_row040_positive
def leaf00447_w_row041 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row041 leaf00447_w_affine)
theorem leaf00447_w_row041_weighted : leaf00447_w_row041=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row041 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row041_identity : leaf00447_w_row041=NestedInteger.coefficientFrom 52 41 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 41 0 leaf00447_w_affine leaf00447_w_row041 IntegerBernsteinWeights52.row041 (IntegerBernsteinTable.checked (n := 2) 52 41 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row041 leaf00447_w_affine_length IntegerBernsteinWeights52.row041_identity) leaf00447_w_row041_weighted
theorem leaf00447_w_row041_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row041=true := by decide +kernel
#print axioms leaf00447_w_row041_weighted
#print axioms leaf00447_w_row041_identity
#print axioms leaf00447_w_row041_positive
def leaf00447_w_row042 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row042 leaf00447_w_affine)
theorem leaf00447_w_row042_weighted : leaf00447_w_row042=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row042 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row042_identity : leaf00447_w_row042=NestedInteger.coefficientFrom 52 42 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 42 0 leaf00447_w_affine leaf00447_w_row042 IntegerBernsteinWeights52.row042 (IntegerBernsteinTable.checked (n := 2) 52 42 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row042 leaf00447_w_affine_length IntegerBernsteinWeights52.row042_identity) leaf00447_w_row042_weighted
theorem leaf00447_w_row042_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row042=true := by decide +kernel
#print axioms leaf00447_w_row042_weighted
#print axioms leaf00447_w_row042_identity
#print axioms leaf00447_w_row042_positive
def leaf00447_w_row043 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row043 leaf00447_w_affine)
theorem leaf00447_w_row043_weighted : leaf00447_w_row043=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row043 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row043_identity : leaf00447_w_row043=NestedInteger.coefficientFrom 52 43 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 43 0 leaf00447_w_affine leaf00447_w_row043 IntegerBernsteinWeights52.row043 (IntegerBernsteinTable.checked (n := 2) 52 43 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row043 leaf00447_w_affine_length IntegerBernsteinWeights52.row043_identity) leaf00447_w_row043_weighted
theorem leaf00447_w_row043_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row043=true := by decide +kernel
#print axioms leaf00447_w_row043_weighted
#print axioms leaf00447_w_row043_identity
#print axioms leaf00447_w_row043_positive
def leaf00447_w_row044 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row044 leaf00447_w_affine)
theorem leaf00447_w_row044_weighted : leaf00447_w_row044=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row044 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row044_identity : leaf00447_w_row044=NestedInteger.coefficientFrom 52 44 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 44 0 leaf00447_w_affine leaf00447_w_row044 IntegerBernsteinWeights52.row044 (IntegerBernsteinTable.checked (n := 2) 52 44 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row044 leaf00447_w_affine_length IntegerBernsteinWeights52.row044_identity) leaf00447_w_row044_weighted
theorem leaf00447_w_row044_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row044=true := by decide +kernel
#print axioms leaf00447_w_row044_weighted
#print axioms leaf00447_w_row044_identity
#print axioms leaf00447_w_row044_positive
def leaf00447_w_row045 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row045 leaf00447_w_affine)
theorem leaf00447_w_row045_weighted : leaf00447_w_row045=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row045 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row045_identity : leaf00447_w_row045=NestedInteger.coefficientFrom 52 45 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 45 0 leaf00447_w_affine leaf00447_w_row045 IntegerBernsteinWeights52.row045 (IntegerBernsteinTable.checked (n := 2) 52 45 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row045 leaf00447_w_affine_length IntegerBernsteinWeights52.row045_identity) leaf00447_w_row045_weighted
theorem leaf00447_w_row045_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row045=true := by decide +kernel
#print axioms leaf00447_w_row045_weighted
#print axioms leaf00447_w_row045_identity
#print axioms leaf00447_w_row045_positive
def leaf00447_w_row046 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row046 leaf00447_w_affine)
theorem leaf00447_w_row046_weighted : leaf00447_w_row046=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row046 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row046_identity : leaf00447_w_row046=NestedInteger.coefficientFrom 52 46 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 46 0 leaf00447_w_affine leaf00447_w_row046 IntegerBernsteinWeights52.row046 (IntegerBernsteinTable.checked (n := 2) 52 46 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row046 leaf00447_w_affine_length IntegerBernsteinWeights52.row046_identity) leaf00447_w_row046_weighted
theorem leaf00447_w_row046_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row046=true := by decide +kernel
#print axioms leaf00447_w_row046_weighted
#print axioms leaf00447_w_row046_identity
#print axioms leaf00447_w_row046_positive
def leaf00447_w_row047 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row047 leaf00447_w_affine)
theorem leaf00447_w_row047_weighted : leaf00447_w_row047=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row047 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row047_identity : leaf00447_w_row047=NestedInteger.coefficientFrom 52 47 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 47 0 leaf00447_w_affine leaf00447_w_row047 IntegerBernsteinWeights52.row047 (IntegerBernsteinTable.checked (n := 2) 52 47 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row047 leaf00447_w_affine_length IntegerBernsteinWeights52.row047_identity) leaf00447_w_row047_weighted
theorem leaf00447_w_row047_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row047=true := by decide +kernel
#print axioms leaf00447_w_row047_weighted
#print axioms leaf00447_w_row047_identity
#print axioms leaf00447_w_row047_positive
def leaf00447_w_row048 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row048 leaf00447_w_affine)
theorem leaf00447_w_row048_weighted : leaf00447_w_row048=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row048 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row048_identity : leaf00447_w_row048=NestedInteger.coefficientFrom 52 48 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 48 0 leaf00447_w_affine leaf00447_w_row048 IntegerBernsteinWeights52.row048 (IntegerBernsteinTable.checked (n := 2) 52 48 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row048 leaf00447_w_affine_length IntegerBernsteinWeights52.row048_identity) leaf00447_w_row048_weighted
theorem leaf00447_w_row048_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row048=true := by decide +kernel
#print axioms leaf00447_w_row048_weighted
#print axioms leaf00447_w_row048_identity
#print axioms leaf00447_w_row048_positive
def leaf00447_w_row049 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row049 leaf00447_w_affine)
theorem leaf00447_w_row049_weighted : leaf00447_w_row049=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row049 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row049_identity : leaf00447_w_row049=NestedInteger.coefficientFrom 52 49 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 49 0 leaf00447_w_affine leaf00447_w_row049 IntegerBernsteinWeights52.row049 (IntegerBernsteinTable.checked (n := 2) 52 49 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row049 leaf00447_w_affine_length IntegerBernsteinWeights52.row049_identity) leaf00447_w_row049_weighted
theorem leaf00447_w_row049_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row049=true := by decide +kernel
#print axioms leaf00447_w_row049_weighted
#print axioms leaf00447_w_row049_identity
#print axioms leaf00447_w_row049_positive
def leaf00447_w_row050 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row050 leaf00447_w_affine)
theorem leaf00447_w_row050_weighted : leaf00447_w_row050=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row050 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row050_identity : leaf00447_w_row050=NestedInteger.coefficientFrom 52 50 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 50 0 leaf00447_w_affine leaf00447_w_row050 IntegerBernsteinWeights52.row050 (IntegerBernsteinTable.checked (n := 2) 52 50 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row050 leaf00447_w_affine_length IntegerBernsteinWeights52.row050_identity) leaf00447_w_row050_weighted
theorem leaf00447_w_row050_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row050=true := by decide +kernel
#print axioms leaf00447_w_row050_weighted
#print axioms leaf00447_w_row050_identity
#print axioms leaf00447_w_row050_positive
def leaf00447_w_row051 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row051 leaf00447_w_affine)
theorem leaf00447_w_row051_weighted : leaf00447_w_row051=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row051 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row051_identity : leaf00447_w_row051=NestedInteger.coefficientFrom 52 51 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 51 0 leaf00447_w_affine leaf00447_w_row051 IntegerBernsteinWeights52.row051 (IntegerBernsteinTable.checked (n := 2) 52 51 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row051 leaf00447_w_affine_length IntegerBernsteinWeights52.row051_identity) leaf00447_w_row051_weighted
theorem leaf00447_w_row051_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row051=true := by decide +kernel
#print axioms leaf00447_w_row051_weighted
#print axioms leaf00447_w_row051_identity
#print axioms leaf00447_w_row051_positive
def leaf00447_w_row052 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row052 leaf00447_w_affine)
theorem leaf00447_w_row052_weighted : leaf00447_w_row052=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights52.row052 leaf00447_w_affine := by decide +kernel
theorem leaf00447_w_row052_identity : leaf00447_w_row052=NestedInteger.coefficientFrom 52 52 0 leaf00447_w_affine :=
  IntegerWeightedBernstein.checked 52 52 0 leaf00447_w_affine leaf00447_w_row052 IntegerBernsteinWeights52.row052 (IntegerBernsteinTable.checked (n := 2) 52 52 0 53 leaf00447_w_affine IntegerBernsteinWeights52.row052 leaf00447_w_affine_length IntegerBernsteinWeights52.row052_identity) leaf00447_w_row052_weighted
theorem leaf00447_w_row052_positive : NestedInteger.bernsteinCheck 2 ![0,4] leaf00447_w_row052=true := by decide +kernel
#print axioms leaf00447_w_row052_weighted
#print axioms leaf00447_w_row052_identity
#print axioms leaf00447_w_row052_positive
def leaf00447_w_rows : Fin 53 → NestedInteger.Poly 2 := ![leaf00447_w_row000,leaf00447_w_row001,leaf00447_w_row002,leaf00447_w_row003,leaf00447_w_row004,leaf00447_w_row005,leaf00447_w_row006,leaf00447_w_row007,leaf00447_w_row008,leaf00447_w_row009,leaf00447_w_row010,leaf00447_w_row011,leaf00447_w_row012,leaf00447_w_row013,leaf00447_w_row014,leaf00447_w_row015,leaf00447_w_row016,leaf00447_w_row017,leaf00447_w_row018,leaf00447_w_row019,leaf00447_w_row020,leaf00447_w_row021,leaf00447_w_row022,leaf00447_w_row023,leaf00447_w_row024,leaf00447_w_row025,leaf00447_w_row026,leaf00447_w_row027,leaf00447_w_row028,leaf00447_w_row029,leaf00447_w_row030,leaf00447_w_row031,leaf00447_w_row032,leaf00447_w_row033,leaf00447_w_row034,leaf00447_w_row035,leaf00447_w_row036,leaf00447_w_row037,leaf00447_w_row038,leaf00447_w_row039,leaf00447_w_row040,leaf00447_w_row041,leaf00447_w_row042,leaf00447_w_row043,leaf00447_w_row044,leaf00447_w_row045,leaf00447_w_row046,leaf00447_w_row047,leaf00447_w_row048,leaf00447_w_row049,leaf00447_w_row050,leaf00447_w_row051,leaf00447_w_row052]
theorem leaf00447_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] leaf00447_w_affine=true := by
  apply IntegerBernsteinRows.checked ![52,0,4] leaf00447_w_affine leaf00447_w_rows (by decide +kernel)
  · intro j
    fin_cases j
    · exact leaf00447_w_row000_identity
    · exact leaf00447_w_row001_identity
    · exact leaf00447_w_row002_identity
    · exact leaf00447_w_row003_identity
    · exact leaf00447_w_row004_identity
    · exact leaf00447_w_row005_identity
    · exact leaf00447_w_row006_identity
    · exact leaf00447_w_row007_identity
    · exact leaf00447_w_row008_identity
    · exact leaf00447_w_row009_identity
    · exact leaf00447_w_row010_identity
    · exact leaf00447_w_row011_identity
    · exact leaf00447_w_row012_identity
    · exact leaf00447_w_row013_identity
    · exact leaf00447_w_row014_identity
    · exact leaf00447_w_row015_identity
    · exact leaf00447_w_row016_identity
    · exact leaf00447_w_row017_identity
    · exact leaf00447_w_row018_identity
    · exact leaf00447_w_row019_identity
    · exact leaf00447_w_row020_identity
    · exact leaf00447_w_row021_identity
    · exact leaf00447_w_row022_identity
    · exact leaf00447_w_row023_identity
    · exact leaf00447_w_row024_identity
    · exact leaf00447_w_row025_identity
    · exact leaf00447_w_row026_identity
    · exact leaf00447_w_row027_identity
    · exact leaf00447_w_row028_identity
    · exact leaf00447_w_row029_identity
    · exact leaf00447_w_row030_identity
    · exact leaf00447_w_row031_identity
    · exact leaf00447_w_row032_identity
    · exact leaf00447_w_row033_identity
    · exact leaf00447_w_row034_identity
    · exact leaf00447_w_row035_identity
    · exact leaf00447_w_row036_identity
    · exact leaf00447_w_row037_identity
    · exact leaf00447_w_row038_identity
    · exact leaf00447_w_row039_identity
    · exact leaf00447_w_row040_identity
    · exact leaf00447_w_row041_identity
    · exact leaf00447_w_row042_identity
    · exact leaf00447_w_row043_identity
    · exact leaf00447_w_row044_identity
    · exact leaf00447_w_row045_identity
    · exact leaf00447_w_row046_identity
    · exact leaf00447_w_row047_identity
    · exact leaf00447_w_row048_identity
    · exact leaf00447_w_row049_identity
    · exact leaf00447_w_row050_identity
    · exact leaf00447_w_row051_identity
    · exact leaf00447_w_row052_identity
  · intro j
    fin_cases j
    · exact leaf00447_w_row000_positive
    · exact leaf00447_w_row001_positive
    · exact leaf00447_w_row002_positive
    · exact leaf00447_w_row003_positive
    · exact leaf00447_w_row004_positive
    · exact leaf00447_w_row005_positive
    · exact leaf00447_w_row006_positive
    · exact leaf00447_w_row007_positive
    · exact leaf00447_w_row008_positive
    · exact leaf00447_w_row009_positive
    · exact leaf00447_w_row010_positive
    · exact leaf00447_w_row011_positive
    · exact leaf00447_w_row012_positive
    · exact leaf00447_w_row013_positive
    · exact leaf00447_w_row014_positive
    · exact leaf00447_w_row015_positive
    · exact leaf00447_w_row016_positive
    · exact leaf00447_w_row017_positive
    · exact leaf00447_w_row018_positive
    · exact leaf00447_w_row019_positive
    · exact leaf00447_w_row020_positive
    · exact leaf00447_w_row021_positive
    · exact leaf00447_w_row022_positive
    · exact leaf00447_w_row023_positive
    · exact leaf00447_w_row024_positive
    · exact leaf00447_w_row025_positive
    · exact leaf00447_w_row026_positive
    · exact leaf00447_w_row027_positive
    · exact leaf00447_w_row028_positive
    · exact leaf00447_w_row029_positive
    · exact leaf00447_w_row030_positive
    · exact leaf00447_w_row031_positive
    · exact leaf00447_w_row032_positive
    · exact leaf00447_w_row033_positive
    · exact leaf00447_w_row034_positive
    · exact leaf00447_w_row035_positive
    · exact leaf00447_w_row036_positive
    · exact leaf00447_w_row037_positive
    · exact leaf00447_w_row038_positive
    · exact leaf00447_w_row039_positive
    · exact leaf00447_w_row040_positive
    · exact leaf00447_w_row041_positive
    · exact leaf00447_w_row042_positive
    · exact leaf00447_w_row043_positive
    · exact leaf00447_w_row044_positive
    · exact leaf00447_w_row045_positive
    · exact leaf00447_w_row046_positive
    · exact leaf00447_w_row047_positive
    · exact leaf00447_w_row048_positive
    · exact leaf00447_w_row049_positive
    · exact leaf00447_w_row050_positive
    · exact leaf00447_w_row051_positive
    · exact leaf00447_w_row052_positive
#print axioms leaf00447_sign
theorem leaf00447_log : RationalLog.accepts (4619836279/4294967296) (78292235/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00447_log
def leaf00447 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack10.pack true (39440043/7812500000) (4619836279/4294967296) (78292235/2147483648) 0 8 ![52,0,4] ![(7/32),0,0] ![(1/64),1,(1/2)] 1323388240920576000000000000 ![64,1,2] leaf00447_w_affine
theorem leaf00447_checked : FastNestedCellData.accepts 1 0 4 leaf00447=true :=
  IntegerPiecewiseCell.accepts_make DegreeOneIntegerNorm10.pack true (39440043/7812500000) (4619836279/4294967296) (78292235/2147483648) 0 8 ![52,0,4] ![(7/32),0,0] ![(1/64),1,(1/2)]
    1323388240920576000000000000 1430674839274636897603139871 283395917743626718726562500000 ![14,0,0] ![1,1,1] ![64,1,2] leaf00447_w_raw leaf00447_w_inner leaf00447_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf00447_raw leaf00447_rectangular leaf00447_inner leaf00447_w_affine_eval leaf00447_sign leaf00447_log
#print axioms leaf00447_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
