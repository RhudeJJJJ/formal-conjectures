/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01233_w_raw : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 15252789286638977024000000000000 19247293864772152925562772684281 338735165631768317776500000000000))
theorem leaf01233_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 15252789286638977024000000000000 19247293864772152925562772684281 338735165631768317776500000000000 leaf01233_w_raw=true := by decide +kernel
theorem leaf01233_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01233_w_raw=true := by decide +kernel
#print axioms leaf01233_raw
#print axioms leaf01233_rectangular
def leaf01233_w_inner : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerAffineStages.inner leaf01233_w_raw ![5,31,30] ![1,1,1] ![8,32,32])
theorem leaf01233_inner : leaf01233_w_inner=IntegerAffineStages.inner leaf01233_w_raw ![5,31,30] ![1,1,1] ![8,32,32] := by decide +kernel
#print axioms leaf01233_inner
def leaf01233_w_source00 : NestedInteger.Poly 3 := leaf01233_w_inner
def leaf01233_w_segment00 : NestedInteger.Poly 3 := leaf01233_w_source00.take 12
def leaf01233_w_weights00 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 0 leaf01233_w_segment00)
theorem leaf01233_w_weights00_identity : leaf01233_w_weights00=IntegerWeightedOuter.weights 5 1 8 0 leaf01233_w_segment00 := by decide +kernel
def leaf01233_w_piece00 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights00 leaf01233_w_segment00)
theorem leaf01233_w_piece00_weighted : leaf01233_w_piece00=IntegerWeightedOuter.applyWeights leaf01233_w_weights00 leaf01233_w_segment00 := by decide +kernel
theorem leaf01233_w_piece00_identity : leaf01233_w_piece00=IntegerOuterTerms.transform 5 1 8 0 leaf01233_w_segment00 :=
  IntegerWeightedOuter.checked 5 1 8 0 leaf01233_w_segment00 leaf01233_w_piece00 leaf01233_w_weights00 leaf01233_w_weights00_identity leaf01233_w_piece00_weighted
#print axioms leaf01233_w_weights00_identity
#print axioms leaf01233_w_piece00_weighted
#print axioms leaf01233_w_piece00_identity
def leaf01233_w_source01 : NestedInteger.Poly 3 := leaf01233_w_source00.drop 12
def leaf01233_w_segment01 : NestedInteger.Poly 3 := leaf01233_w_source01.take 12
def leaf01233_w_weights01 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 12 leaf01233_w_segment01)
theorem leaf01233_w_weights01_identity : leaf01233_w_weights01=IntegerWeightedOuter.weights 5 1 8 12 leaf01233_w_segment01 := by decide +kernel
def leaf01233_w_piece01 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights01 leaf01233_w_segment01)
theorem leaf01233_w_piece01_weighted : leaf01233_w_piece01=IntegerWeightedOuter.applyWeights leaf01233_w_weights01 leaf01233_w_segment01 := by decide +kernel
theorem leaf01233_w_piece01_identity : leaf01233_w_piece01=IntegerOuterTerms.transform 5 1 8 12 leaf01233_w_segment01 :=
  IntegerWeightedOuter.checked 5 1 8 12 leaf01233_w_segment01 leaf01233_w_piece01 leaf01233_w_weights01 leaf01233_w_weights01_identity leaf01233_w_piece01_weighted
#print axioms leaf01233_w_weights01_identity
#print axioms leaf01233_w_piece01_weighted
#print axioms leaf01233_w_piece01_identity
def leaf01233_w_source02 : NestedInteger.Poly 3 := leaf01233_w_source01.drop 12
def leaf01233_w_segment02 : NestedInteger.Poly 3 := leaf01233_w_source02.take 12
def leaf01233_w_weights02 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 24 leaf01233_w_segment02)
theorem leaf01233_w_weights02_identity : leaf01233_w_weights02=IntegerWeightedOuter.weights 5 1 8 24 leaf01233_w_segment02 := by decide +kernel
def leaf01233_w_piece02 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights02 leaf01233_w_segment02)
theorem leaf01233_w_piece02_weighted : leaf01233_w_piece02=IntegerWeightedOuter.applyWeights leaf01233_w_weights02 leaf01233_w_segment02 := by decide +kernel
theorem leaf01233_w_piece02_identity : leaf01233_w_piece02=IntegerOuterTerms.transform 5 1 8 24 leaf01233_w_segment02 :=
  IntegerWeightedOuter.checked 5 1 8 24 leaf01233_w_segment02 leaf01233_w_piece02 leaf01233_w_weights02 leaf01233_w_weights02_identity leaf01233_w_piece02_weighted
#print axioms leaf01233_w_weights02_identity
#print axioms leaf01233_w_piece02_weighted
#print axioms leaf01233_w_piece02_identity
def leaf01233_w_source03 : NestedInteger.Poly 3 := leaf01233_w_source02.drop 12
def leaf01233_w_segment03 : NestedInteger.Poly 3 := leaf01233_w_source03.take 12
def leaf01233_w_weights03 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 36 leaf01233_w_segment03)
theorem leaf01233_w_weights03_identity : leaf01233_w_weights03=IntegerWeightedOuter.weights 5 1 8 36 leaf01233_w_segment03 := by decide +kernel
def leaf01233_w_piece03 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights03 leaf01233_w_segment03)
theorem leaf01233_w_piece03_weighted : leaf01233_w_piece03=IntegerWeightedOuter.applyWeights leaf01233_w_weights03 leaf01233_w_segment03 := by decide +kernel
theorem leaf01233_w_piece03_identity : leaf01233_w_piece03=IntegerOuterTerms.transform 5 1 8 36 leaf01233_w_segment03 :=
  IntegerWeightedOuter.checked 5 1 8 36 leaf01233_w_segment03 leaf01233_w_piece03 leaf01233_w_weights03 leaf01233_w_weights03_identity leaf01233_w_piece03_weighted
#print axioms leaf01233_w_weights03_identity
#print axioms leaf01233_w_piece03_weighted
#print axioms leaf01233_w_piece03_identity
def leaf01233_w_source04 : NestedInteger.Poly 3 := leaf01233_w_source03.drop 12
def leaf01233_w_segment04 : NestedInteger.Poly 3 := leaf01233_w_source04.take 12
def leaf01233_w_weights04 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 48 leaf01233_w_segment04)
theorem leaf01233_w_weights04_identity : leaf01233_w_weights04=IntegerWeightedOuter.weights 5 1 8 48 leaf01233_w_segment04 := by decide +kernel
def leaf01233_w_piece04 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights04 leaf01233_w_segment04)
theorem leaf01233_w_piece04_weighted : leaf01233_w_piece04=IntegerWeightedOuter.applyWeights leaf01233_w_weights04 leaf01233_w_segment04 := by decide +kernel
theorem leaf01233_w_piece04_identity : leaf01233_w_piece04=IntegerOuterTerms.transform 5 1 8 48 leaf01233_w_segment04 :=
  IntegerWeightedOuter.checked 5 1 8 48 leaf01233_w_segment04 leaf01233_w_piece04 leaf01233_w_weights04 leaf01233_w_weights04_identity leaf01233_w_piece04_weighted
#print axioms leaf01233_w_weights04_identity
#print axioms leaf01233_w_piece04_weighted
#print axioms leaf01233_w_piece04_identity
def leaf01233_w_source05 : NestedInteger.Poly 3 := leaf01233_w_source04.drop 12
def leaf01233_w_segment05 : NestedInteger.Poly 3 := leaf01233_w_source05.take 12
def leaf01233_w_weights05 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 60 leaf01233_w_segment05)
theorem leaf01233_w_weights05_identity : leaf01233_w_weights05=IntegerWeightedOuter.weights 5 1 8 60 leaf01233_w_segment05 := by decide +kernel
def leaf01233_w_piece05 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights05 leaf01233_w_segment05)
theorem leaf01233_w_piece05_weighted : leaf01233_w_piece05=IntegerWeightedOuter.applyWeights leaf01233_w_weights05 leaf01233_w_segment05 := by decide +kernel
theorem leaf01233_w_piece05_identity : leaf01233_w_piece05=IntegerOuterTerms.transform 5 1 8 60 leaf01233_w_segment05 :=
  IntegerWeightedOuter.checked 5 1 8 60 leaf01233_w_segment05 leaf01233_w_piece05 leaf01233_w_weights05 leaf01233_w_weights05_identity leaf01233_w_piece05_weighted
#print axioms leaf01233_w_weights05_identity
#print axioms leaf01233_w_piece05_weighted
#print axioms leaf01233_w_piece05_identity
def leaf01233_w_source06 : NestedInteger.Poly 3 := leaf01233_w_source05.drop 12
def leaf01233_w_segment06 : NestedInteger.Poly 3 := leaf01233_w_source06.take 12
def leaf01233_w_weights06 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 72 leaf01233_w_segment06)
theorem leaf01233_w_weights06_identity : leaf01233_w_weights06=IntegerWeightedOuter.weights 5 1 8 72 leaf01233_w_segment06 := by decide +kernel
def leaf01233_w_piece06 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights06 leaf01233_w_segment06)
theorem leaf01233_w_piece06_weighted : leaf01233_w_piece06=IntegerWeightedOuter.applyWeights leaf01233_w_weights06 leaf01233_w_segment06 := by decide +kernel
theorem leaf01233_w_piece06_identity : leaf01233_w_piece06=IntegerOuterTerms.transform 5 1 8 72 leaf01233_w_segment06 :=
  IntegerWeightedOuter.checked 5 1 8 72 leaf01233_w_segment06 leaf01233_w_piece06 leaf01233_w_weights06 leaf01233_w_weights06_identity leaf01233_w_piece06_weighted
#print axioms leaf01233_w_weights06_identity
#print axioms leaf01233_w_piece06_weighted
#print axioms leaf01233_w_piece06_identity
def leaf01233_w_source07 : NestedInteger.Poly 3 := leaf01233_w_source06.drop 12
def leaf01233_w_segment07 : NestedInteger.Poly 3 := leaf01233_w_source07.take 12
def leaf01233_w_weights07 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 5 1 8 84 leaf01233_w_segment07)
theorem leaf01233_w_weights07_identity : leaf01233_w_weights07=IntegerWeightedOuter.weights 5 1 8 84 leaf01233_w_segment07 := by decide +kernel
def leaf01233_w_piece07 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01233_w_weights07 leaf01233_w_segment07)
theorem leaf01233_w_piece07_weighted : leaf01233_w_piece07=IntegerWeightedOuter.applyWeights leaf01233_w_weights07 leaf01233_w_segment07 := by decide +kernel
theorem leaf01233_w_piece07_identity : leaf01233_w_piece07=IntegerOuterTerms.transform 5 1 8 84 leaf01233_w_segment07 :=
  IntegerWeightedOuter.checked 5 1 8 84 leaf01233_w_segment07 leaf01233_w_piece07 leaf01233_w_weights07 leaf01233_w_weights07_identity leaf01233_w_piece07_weighted
#print axioms leaf01233_w_weights07_identity
#print axioms leaf01233_w_piece07_weighted
#print axioms leaf01233_w_piece07_identity
def leaf01233_w_suffix07 : NestedInteger.Poly 3 := leaf01233_w_piece07
theorem leaf01233_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 84 leaf01233_w_source07)) x := by
  have h : leaf01233_w_segment07=leaf01233_w_source07 := by decide +kernel
  rw [leaf01233_w_suffix07,leaf01233_w_piece07_identity,h]
#print axioms leaf01233_w_suffix07_eval
def leaf01233_w_suffix06 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source07.length) leaf01233_w_piece06) leaf01233_w_suffix07)
theorem leaf01233_w_suffix06_join : leaf01233_w_suffix06=NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source07.length) leaf01233_w_piece06) leaf01233_w_suffix07 := by decide +kernel
theorem leaf01233_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 72 leaf01233_w_source06)) x := by
  have hlen : leaf01233_w_segment06.length=12 := by decide +kernel
  calc
    _ = (8 : ℝ)^leaf01233_w_source07.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 72 leaf01233_w_segment06)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 (72+leaf01233_w_segment06.length) leaf01233_w_source07)) x := by
      rw [leaf01233_w_suffix06_join,cast_add,eval_add,cast_scale,eval_scale,leaf01233_w_piece06_identity,leaf01233_w_suffix07_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 72 (leaf01233_w_segment06++leaf01233_w_source07))) x :=
      (IntegerOuterPieces.eval_append 5 1 8 72 leaf01233_w_segment06 leaf01233_w_source07 x).symm
    _ = _ := by rw [show leaf01233_w_segment06++leaf01233_w_source07=leaf01233_w_source06 from List.take_append_drop 12 leaf01233_w_source06]
#print axioms leaf01233_w_suffix06_join
#print axioms leaf01233_w_suffix06_eval
def leaf01233_w_suffix05 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source06.length) leaf01233_w_piece05) leaf01233_w_suffix06)
theorem leaf01233_w_suffix05_join : leaf01233_w_suffix05=NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source06.length) leaf01233_w_piece05) leaf01233_w_suffix06 := by decide +kernel
theorem leaf01233_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 60 leaf01233_w_source05)) x := by
  have hlen : leaf01233_w_segment05.length=12 := by decide +kernel
  calc
    _ = (8 : ℝ)^leaf01233_w_source06.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 60 leaf01233_w_segment05)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 (60+leaf01233_w_segment05.length) leaf01233_w_source06)) x := by
      rw [leaf01233_w_suffix05_join,cast_add,eval_add,cast_scale,eval_scale,leaf01233_w_piece05_identity,leaf01233_w_suffix06_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 60 (leaf01233_w_segment05++leaf01233_w_source06))) x :=
      (IntegerOuterPieces.eval_append 5 1 8 60 leaf01233_w_segment05 leaf01233_w_source06 x).symm
    _ = _ := by rw [show leaf01233_w_segment05++leaf01233_w_source06=leaf01233_w_source05 from List.take_append_drop 12 leaf01233_w_source05]
#print axioms leaf01233_w_suffix05_join
#print axioms leaf01233_w_suffix05_eval
def leaf01233_w_suffix04 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source05.length) leaf01233_w_piece04) leaf01233_w_suffix05)
theorem leaf01233_w_suffix04_join : leaf01233_w_suffix04=NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source05.length) leaf01233_w_piece04) leaf01233_w_suffix05 := by decide +kernel
theorem leaf01233_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 48 leaf01233_w_source04)) x := by
  have hlen : leaf01233_w_segment04.length=12 := by decide +kernel
  calc
    _ = (8 : ℝ)^leaf01233_w_source05.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 48 leaf01233_w_segment04)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 (48+leaf01233_w_segment04.length) leaf01233_w_source05)) x := by
      rw [leaf01233_w_suffix04_join,cast_add,eval_add,cast_scale,eval_scale,leaf01233_w_piece04_identity,leaf01233_w_suffix05_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 48 (leaf01233_w_segment04++leaf01233_w_source05))) x :=
      (IntegerOuterPieces.eval_append 5 1 8 48 leaf01233_w_segment04 leaf01233_w_source05 x).symm
    _ = _ := by rw [show leaf01233_w_segment04++leaf01233_w_source05=leaf01233_w_source04 from List.take_append_drop 12 leaf01233_w_source04]
#print axioms leaf01233_w_suffix04_join
#print axioms leaf01233_w_suffix04_eval
def leaf01233_w_suffix03 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source04.length) leaf01233_w_piece03) leaf01233_w_suffix04)
theorem leaf01233_w_suffix03_join : leaf01233_w_suffix03=NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source04.length) leaf01233_w_piece03) leaf01233_w_suffix04 := by decide +kernel
theorem leaf01233_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 36 leaf01233_w_source03)) x := by
  have hlen : leaf01233_w_segment03.length=12 := by decide +kernel
  calc
    _ = (8 : ℝ)^leaf01233_w_source04.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 36 leaf01233_w_segment03)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 (36+leaf01233_w_segment03.length) leaf01233_w_source04)) x := by
      rw [leaf01233_w_suffix03_join,cast_add,eval_add,cast_scale,eval_scale,leaf01233_w_piece03_identity,leaf01233_w_suffix04_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 36 (leaf01233_w_segment03++leaf01233_w_source04))) x :=
      (IntegerOuterPieces.eval_append 5 1 8 36 leaf01233_w_segment03 leaf01233_w_source04 x).symm
    _ = _ := by rw [show leaf01233_w_segment03++leaf01233_w_source04=leaf01233_w_source03 from List.take_append_drop 12 leaf01233_w_source03]
#print axioms leaf01233_w_suffix03_join
#print axioms leaf01233_w_suffix03_eval
def leaf01233_w_suffix02 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source03.length) leaf01233_w_piece02) leaf01233_w_suffix03)
theorem leaf01233_w_suffix02_join : leaf01233_w_suffix02=NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source03.length) leaf01233_w_piece02) leaf01233_w_suffix03 := by decide +kernel
theorem leaf01233_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 24 leaf01233_w_source02)) x := by
  have hlen : leaf01233_w_segment02.length=12 := by decide +kernel
  calc
    _ = (8 : ℝ)^leaf01233_w_source03.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 24 leaf01233_w_segment02)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 (24+leaf01233_w_segment02.length) leaf01233_w_source03)) x := by
      rw [leaf01233_w_suffix02_join,cast_add,eval_add,cast_scale,eval_scale,leaf01233_w_piece02_identity,leaf01233_w_suffix03_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 24 (leaf01233_w_segment02++leaf01233_w_source03))) x :=
      (IntegerOuterPieces.eval_append 5 1 8 24 leaf01233_w_segment02 leaf01233_w_source03 x).symm
    _ = _ := by rw [show leaf01233_w_segment02++leaf01233_w_source03=leaf01233_w_source02 from List.take_append_drop 12 leaf01233_w_source02]
#print axioms leaf01233_w_suffix02_join
#print axioms leaf01233_w_suffix02_eval
def leaf01233_w_suffix01 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source02.length) leaf01233_w_piece01) leaf01233_w_suffix02)
theorem leaf01233_w_suffix01_join : leaf01233_w_suffix01=NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source02.length) leaf01233_w_piece01) leaf01233_w_suffix02 := by decide +kernel
theorem leaf01233_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 12 leaf01233_w_source01)) x := by
  have hlen : leaf01233_w_segment01.length=12 := by decide +kernel
  calc
    _ = (8 : ℝ)^leaf01233_w_source02.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 12 leaf01233_w_segment01)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 (12+leaf01233_w_segment01.length) leaf01233_w_source02)) x := by
      rw [leaf01233_w_suffix01_join,cast_add,eval_add,cast_scale,eval_scale,leaf01233_w_piece01_identity,leaf01233_w_suffix02_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 12 (leaf01233_w_segment01++leaf01233_w_source02))) x :=
      (IntegerOuterPieces.eval_append 5 1 8 12 leaf01233_w_segment01 leaf01233_w_source02 x).symm
    _ = _ := by rw [show leaf01233_w_segment01++leaf01233_w_source02=leaf01233_w_source01 from List.take_append_drop 12 leaf01233_w_source01]
#print axioms leaf01233_w_suffix01_join
#print axioms leaf01233_w_suffix01_eval
def leaf01233_w_affine : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source01.length) leaf01233_w_piece00) leaf01233_w_suffix01)
theorem leaf01233_w_affine_join : leaf01233_w_affine=NestedInteger.add (NestedInteger.scale (8^leaf01233_w_source01.length) leaf01233_w_piece00) leaf01233_w_suffix01 := by decide +kernel
theorem leaf01233_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01233_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 0 leaf01233_w_source00)) x := by
  have hlen : leaf01233_w_segment00.length=12 := by decide +kernel
  calc
    _ = (8 : ℝ)^leaf01233_w_source01.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 0 leaf01233_w_segment00)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 (0+leaf01233_w_segment00.length) leaf01233_w_source01)) x := by
      rw [leaf01233_w_affine_join,cast_add,eval_add,cast_scale,eval_scale,leaf01233_w_piece00_identity,leaf01233_w_suffix01_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 5 1 8 0 (leaf01233_w_segment00++leaf01233_w_source01))) x :=
      (IntegerOuterPieces.eval_append 5 1 8 0 leaf01233_w_segment00 leaf01233_w_source01 x).symm
    _ = _ := by rw [show leaf01233_w_segment00++leaf01233_w_source01=leaf01233_w_source00 from List.take_append_drop 12 leaf01233_w_source00]
#print axioms leaf01233_w_affine_join
#print axioms leaf01233_w_affine_eval
theorem leaf01233_w_affine_length : leaf01233_w_affine.length=89 := by decide +kernel
#print axioms leaf01233_w_affine_length
def leaf01233_w_row000 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01233_w_affine)
theorem leaf01233_w_row000_weighted : leaf01233_w_row000=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row000_identity : leaf01233_w_row000=NestedInteger.coefficientFrom 88 0 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 0 0 leaf01233_w_affine leaf01233_w_row000 IntegerBernsteinWeights88.row000 (IntegerBernsteinTable.checked (n := 2) 88 0 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row000 leaf01233_w_affine_length IntegerBernsteinWeights88.row000_identity) leaf01233_w_row000_weighted
theorem leaf01233_w_row000_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row000=true := by decide +kernel
#print axioms leaf01233_w_row000_weighted
#print axioms leaf01233_w_row000_identity
#print axioms leaf01233_w_row000_positive
def leaf01233_w_row001 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01233_w_affine)
theorem leaf01233_w_row001_weighted : leaf01233_w_row001=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row001_identity : leaf01233_w_row001=NestedInteger.coefficientFrom 88 1 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 1 0 leaf01233_w_affine leaf01233_w_row001 IntegerBernsteinWeights88.row001 (IntegerBernsteinTable.checked (n := 2) 88 1 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row001 leaf01233_w_affine_length IntegerBernsteinWeights88.row001_identity) leaf01233_w_row001_weighted
theorem leaf01233_w_row001_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row001=true := by decide +kernel
#print axioms leaf01233_w_row001_weighted
#print axioms leaf01233_w_row001_identity
#print axioms leaf01233_w_row001_positive
def leaf01233_w_row002 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01233_w_affine)
theorem leaf01233_w_row002_weighted : leaf01233_w_row002=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row002_identity : leaf01233_w_row002=NestedInteger.coefficientFrom 88 2 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 2 0 leaf01233_w_affine leaf01233_w_row002 IntegerBernsteinWeights88.row002 (IntegerBernsteinTable.checked (n := 2) 88 2 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row002 leaf01233_w_affine_length IntegerBernsteinWeights88.row002_identity) leaf01233_w_row002_weighted
theorem leaf01233_w_row002_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row002=true := by decide +kernel
#print axioms leaf01233_w_row002_weighted
#print axioms leaf01233_w_row002_identity
#print axioms leaf01233_w_row002_positive
def leaf01233_w_row003 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01233_w_affine)
theorem leaf01233_w_row003_weighted : leaf01233_w_row003=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row003_identity : leaf01233_w_row003=NestedInteger.coefficientFrom 88 3 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 3 0 leaf01233_w_affine leaf01233_w_row003 IntegerBernsteinWeights88.row003 (IntegerBernsteinTable.checked (n := 2) 88 3 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row003 leaf01233_w_affine_length IntegerBernsteinWeights88.row003_identity) leaf01233_w_row003_weighted
theorem leaf01233_w_row003_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row003=true := by decide +kernel
#print axioms leaf01233_w_row003_weighted
#print axioms leaf01233_w_row003_identity
#print axioms leaf01233_w_row003_positive
def leaf01233_w_row004 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01233_w_affine)
theorem leaf01233_w_row004_weighted : leaf01233_w_row004=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row004_identity : leaf01233_w_row004=NestedInteger.coefficientFrom 88 4 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 4 0 leaf01233_w_affine leaf01233_w_row004 IntegerBernsteinWeights88.row004 (IntegerBernsteinTable.checked (n := 2) 88 4 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row004 leaf01233_w_affine_length IntegerBernsteinWeights88.row004_identity) leaf01233_w_row004_weighted
theorem leaf01233_w_row004_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row004=true := by decide +kernel
#print axioms leaf01233_w_row004_weighted
#print axioms leaf01233_w_row004_identity
#print axioms leaf01233_w_row004_positive
def leaf01233_w_row005 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01233_w_affine)
theorem leaf01233_w_row005_weighted : leaf01233_w_row005=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row005_identity : leaf01233_w_row005=NestedInteger.coefficientFrom 88 5 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 5 0 leaf01233_w_affine leaf01233_w_row005 IntegerBernsteinWeights88.row005 (IntegerBernsteinTable.checked (n := 2) 88 5 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row005 leaf01233_w_affine_length IntegerBernsteinWeights88.row005_identity) leaf01233_w_row005_weighted
theorem leaf01233_w_row005_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row005=true := by decide +kernel
#print axioms leaf01233_w_row005_weighted
#print axioms leaf01233_w_row005_identity
#print axioms leaf01233_w_row005_positive
def leaf01233_w_row006 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01233_w_affine)
theorem leaf01233_w_row006_weighted : leaf01233_w_row006=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row006_identity : leaf01233_w_row006=NestedInteger.coefficientFrom 88 6 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 6 0 leaf01233_w_affine leaf01233_w_row006 IntegerBernsteinWeights88.row006 (IntegerBernsteinTable.checked (n := 2) 88 6 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row006 leaf01233_w_affine_length IntegerBernsteinWeights88.row006_identity) leaf01233_w_row006_weighted
theorem leaf01233_w_row006_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row006=true := by decide +kernel
#print axioms leaf01233_w_row006_weighted
#print axioms leaf01233_w_row006_identity
#print axioms leaf01233_w_row006_positive
def leaf01233_w_row007 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01233_w_affine)
theorem leaf01233_w_row007_weighted : leaf01233_w_row007=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row007_identity : leaf01233_w_row007=NestedInteger.coefficientFrom 88 7 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 7 0 leaf01233_w_affine leaf01233_w_row007 IntegerBernsteinWeights88.row007 (IntegerBernsteinTable.checked (n := 2) 88 7 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row007 leaf01233_w_affine_length IntegerBernsteinWeights88.row007_identity) leaf01233_w_row007_weighted
theorem leaf01233_w_row007_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row007=true := by decide +kernel
#print axioms leaf01233_w_row007_weighted
#print axioms leaf01233_w_row007_identity
#print axioms leaf01233_w_row007_positive
def leaf01233_w_row008 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01233_w_affine)
theorem leaf01233_w_row008_weighted : leaf01233_w_row008=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row008_identity : leaf01233_w_row008=NestedInteger.coefficientFrom 88 8 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 8 0 leaf01233_w_affine leaf01233_w_row008 IntegerBernsteinWeights88.row008 (IntegerBernsteinTable.checked (n := 2) 88 8 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row008 leaf01233_w_affine_length IntegerBernsteinWeights88.row008_identity) leaf01233_w_row008_weighted
theorem leaf01233_w_row008_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row008=true := by decide +kernel
#print axioms leaf01233_w_row008_weighted
#print axioms leaf01233_w_row008_identity
#print axioms leaf01233_w_row008_positive
def leaf01233_w_row009 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01233_w_affine)
theorem leaf01233_w_row009_weighted : leaf01233_w_row009=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row009_identity : leaf01233_w_row009=NestedInteger.coefficientFrom 88 9 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 9 0 leaf01233_w_affine leaf01233_w_row009 IntegerBernsteinWeights88.row009 (IntegerBernsteinTable.checked (n := 2) 88 9 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row009 leaf01233_w_affine_length IntegerBernsteinWeights88.row009_identity) leaf01233_w_row009_weighted
theorem leaf01233_w_row009_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row009=true := by decide +kernel
#print axioms leaf01233_w_row009_weighted
#print axioms leaf01233_w_row009_identity
#print axioms leaf01233_w_row009_positive
def leaf01233_w_row010 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01233_w_affine)
theorem leaf01233_w_row010_weighted : leaf01233_w_row010=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row010_identity : leaf01233_w_row010=NestedInteger.coefficientFrom 88 10 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 10 0 leaf01233_w_affine leaf01233_w_row010 IntegerBernsteinWeights88.row010 (IntegerBernsteinTable.checked (n := 2) 88 10 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row010 leaf01233_w_affine_length IntegerBernsteinWeights88.row010_identity) leaf01233_w_row010_weighted
theorem leaf01233_w_row010_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row010=true := by decide +kernel
#print axioms leaf01233_w_row010_weighted
#print axioms leaf01233_w_row010_identity
#print axioms leaf01233_w_row010_positive
def leaf01233_w_row011 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01233_w_affine)
theorem leaf01233_w_row011_weighted : leaf01233_w_row011=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row011_identity : leaf01233_w_row011=NestedInteger.coefficientFrom 88 11 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 11 0 leaf01233_w_affine leaf01233_w_row011 IntegerBernsteinWeights88.row011 (IntegerBernsteinTable.checked (n := 2) 88 11 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row011 leaf01233_w_affine_length IntegerBernsteinWeights88.row011_identity) leaf01233_w_row011_weighted
theorem leaf01233_w_row011_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row011=true := by decide +kernel
#print axioms leaf01233_w_row011_weighted
#print axioms leaf01233_w_row011_identity
#print axioms leaf01233_w_row011_positive
def leaf01233_w_row012 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01233_w_affine)
theorem leaf01233_w_row012_weighted : leaf01233_w_row012=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row012_identity : leaf01233_w_row012=NestedInteger.coefficientFrom 88 12 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 12 0 leaf01233_w_affine leaf01233_w_row012 IntegerBernsteinWeights88.row012 (IntegerBernsteinTable.checked (n := 2) 88 12 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row012 leaf01233_w_affine_length IntegerBernsteinWeights88.row012_identity) leaf01233_w_row012_weighted
theorem leaf01233_w_row012_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row012=true := by decide +kernel
#print axioms leaf01233_w_row012_weighted
#print axioms leaf01233_w_row012_identity
#print axioms leaf01233_w_row012_positive
def leaf01233_w_row013 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01233_w_affine)
theorem leaf01233_w_row013_weighted : leaf01233_w_row013=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row013_identity : leaf01233_w_row013=NestedInteger.coefficientFrom 88 13 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 13 0 leaf01233_w_affine leaf01233_w_row013 IntegerBernsteinWeights88.row013 (IntegerBernsteinTable.checked (n := 2) 88 13 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row013 leaf01233_w_affine_length IntegerBernsteinWeights88.row013_identity) leaf01233_w_row013_weighted
theorem leaf01233_w_row013_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row013=true := by decide +kernel
#print axioms leaf01233_w_row013_weighted
#print axioms leaf01233_w_row013_identity
#print axioms leaf01233_w_row013_positive
def leaf01233_w_row014 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01233_w_affine)
theorem leaf01233_w_row014_weighted : leaf01233_w_row014=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row014_identity : leaf01233_w_row014=NestedInteger.coefficientFrom 88 14 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 14 0 leaf01233_w_affine leaf01233_w_row014 IntegerBernsteinWeights88.row014 (IntegerBernsteinTable.checked (n := 2) 88 14 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row014 leaf01233_w_affine_length IntegerBernsteinWeights88.row014_identity) leaf01233_w_row014_weighted
theorem leaf01233_w_row014_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row014=true := by decide +kernel
#print axioms leaf01233_w_row014_weighted
#print axioms leaf01233_w_row014_identity
#print axioms leaf01233_w_row014_positive
def leaf01233_w_row015 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01233_w_affine)
theorem leaf01233_w_row015_weighted : leaf01233_w_row015=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row015_identity : leaf01233_w_row015=NestedInteger.coefficientFrom 88 15 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 15 0 leaf01233_w_affine leaf01233_w_row015 IntegerBernsteinWeights88.row015 (IntegerBernsteinTable.checked (n := 2) 88 15 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row015 leaf01233_w_affine_length IntegerBernsteinWeights88.row015_identity) leaf01233_w_row015_weighted
theorem leaf01233_w_row015_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row015=true := by decide +kernel
#print axioms leaf01233_w_row015_weighted
#print axioms leaf01233_w_row015_identity
#print axioms leaf01233_w_row015_positive
def leaf01233_w_row016 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01233_w_affine)
theorem leaf01233_w_row016_weighted : leaf01233_w_row016=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row016_identity : leaf01233_w_row016=NestedInteger.coefficientFrom 88 16 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 16 0 leaf01233_w_affine leaf01233_w_row016 IntegerBernsteinWeights88.row016 (IntegerBernsteinTable.checked (n := 2) 88 16 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row016 leaf01233_w_affine_length IntegerBernsteinWeights88.row016_identity) leaf01233_w_row016_weighted
theorem leaf01233_w_row016_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row016=true := by decide +kernel
#print axioms leaf01233_w_row016_weighted
#print axioms leaf01233_w_row016_identity
#print axioms leaf01233_w_row016_positive
def leaf01233_w_row017 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01233_w_affine)
theorem leaf01233_w_row017_weighted : leaf01233_w_row017=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row017_identity : leaf01233_w_row017=NestedInteger.coefficientFrom 88 17 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 17 0 leaf01233_w_affine leaf01233_w_row017 IntegerBernsteinWeights88.row017 (IntegerBernsteinTable.checked (n := 2) 88 17 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row017 leaf01233_w_affine_length IntegerBernsteinWeights88.row017_identity) leaf01233_w_row017_weighted
theorem leaf01233_w_row017_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row017=true := by decide +kernel
#print axioms leaf01233_w_row017_weighted
#print axioms leaf01233_w_row017_identity
#print axioms leaf01233_w_row017_positive
def leaf01233_w_row018 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01233_w_affine)
theorem leaf01233_w_row018_weighted : leaf01233_w_row018=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row018_identity : leaf01233_w_row018=NestedInteger.coefficientFrom 88 18 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 18 0 leaf01233_w_affine leaf01233_w_row018 IntegerBernsteinWeights88.row018 (IntegerBernsteinTable.checked (n := 2) 88 18 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row018 leaf01233_w_affine_length IntegerBernsteinWeights88.row018_identity) leaf01233_w_row018_weighted
theorem leaf01233_w_row018_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row018=true := by decide +kernel
#print axioms leaf01233_w_row018_weighted
#print axioms leaf01233_w_row018_identity
#print axioms leaf01233_w_row018_positive
def leaf01233_w_row019 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01233_w_affine)
theorem leaf01233_w_row019_weighted : leaf01233_w_row019=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row019_identity : leaf01233_w_row019=NestedInteger.coefficientFrom 88 19 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 19 0 leaf01233_w_affine leaf01233_w_row019 IntegerBernsteinWeights88.row019 (IntegerBernsteinTable.checked (n := 2) 88 19 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row019 leaf01233_w_affine_length IntegerBernsteinWeights88.row019_identity) leaf01233_w_row019_weighted
theorem leaf01233_w_row019_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row019=true := by decide +kernel
#print axioms leaf01233_w_row019_weighted
#print axioms leaf01233_w_row019_identity
#print axioms leaf01233_w_row019_positive
def leaf01233_w_row020 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01233_w_affine)
theorem leaf01233_w_row020_weighted : leaf01233_w_row020=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row020_identity : leaf01233_w_row020=NestedInteger.coefficientFrom 88 20 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 20 0 leaf01233_w_affine leaf01233_w_row020 IntegerBernsteinWeights88.row020 (IntegerBernsteinTable.checked (n := 2) 88 20 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row020 leaf01233_w_affine_length IntegerBernsteinWeights88.row020_identity) leaf01233_w_row020_weighted
theorem leaf01233_w_row020_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row020=true := by decide +kernel
#print axioms leaf01233_w_row020_weighted
#print axioms leaf01233_w_row020_identity
#print axioms leaf01233_w_row020_positive
def leaf01233_w_row021 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01233_w_affine)
theorem leaf01233_w_row021_weighted : leaf01233_w_row021=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row021_identity : leaf01233_w_row021=NestedInteger.coefficientFrom 88 21 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 21 0 leaf01233_w_affine leaf01233_w_row021 IntegerBernsteinWeights88.row021 (IntegerBernsteinTable.checked (n := 2) 88 21 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row021 leaf01233_w_affine_length IntegerBernsteinWeights88.row021_identity) leaf01233_w_row021_weighted
theorem leaf01233_w_row021_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row021=true := by decide +kernel
#print axioms leaf01233_w_row021_weighted
#print axioms leaf01233_w_row021_identity
#print axioms leaf01233_w_row021_positive
def leaf01233_w_row022 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01233_w_affine)
theorem leaf01233_w_row022_weighted : leaf01233_w_row022=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row022_identity : leaf01233_w_row022=NestedInteger.coefficientFrom 88 22 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 22 0 leaf01233_w_affine leaf01233_w_row022 IntegerBernsteinWeights88.row022 (IntegerBernsteinTable.checked (n := 2) 88 22 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row022 leaf01233_w_affine_length IntegerBernsteinWeights88.row022_identity) leaf01233_w_row022_weighted
theorem leaf01233_w_row022_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row022=true := by decide +kernel
#print axioms leaf01233_w_row022_weighted
#print axioms leaf01233_w_row022_identity
#print axioms leaf01233_w_row022_positive
def leaf01233_w_row023 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01233_w_affine)
theorem leaf01233_w_row023_weighted : leaf01233_w_row023=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row023_identity : leaf01233_w_row023=NestedInteger.coefficientFrom 88 23 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 23 0 leaf01233_w_affine leaf01233_w_row023 IntegerBernsteinWeights88.row023 (IntegerBernsteinTable.checked (n := 2) 88 23 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row023 leaf01233_w_affine_length IntegerBernsteinWeights88.row023_identity) leaf01233_w_row023_weighted
theorem leaf01233_w_row023_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row023=true := by decide +kernel
#print axioms leaf01233_w_row023_weighted
#print axioms leaf01233_w_row023_identity
#print axioms leaf01233_w_row023_positive
def leaf01233_w_row024 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01233_w_affine)
theorem leaf01233_w_row024_weighted : leaf01233_w_row024=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row024_identity : leaf01233_w_row024=NestedInteger.coefficientFrom 88 24 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 24 0 leaf01233_w_affine leaf01233_w_row024 IntegerBernsteinWeights88.row024 (IntegerBernsteinTable.checked (n := 2) 88 24 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row024 leaf01233_w_affine_length IntegerBernsteinWeights88.row024_identity) leaf01233_w_row024_weighted
theorem leaf01233_w_row024_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row024=true := by decide +kernel
#print axioms leaf01233_w_row024_weighted
#print axioms leaf01233_w_row024_identity
#print axioms leaf01233_w_row024_positive
def leaf01233_w_row025 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01233_w_affine)
theorem leaf01233_w_row025_weighted : leaf01233_w_row025=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row025_identity : leaf01233_w_row025=NestedInteger.coefficientFrom 88 25 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 25 0 leaf01233_w_affine leaf01233_w_row025 IntegerBernsteinWeights88.row025 (IntegerBernsteinTable.checked (n := 2) 88 25 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row025 leaf01233_w_affine_length IntegerBernsteinWeights88.row025_identity) leaf01233_w_row025_weighted
theorem leaf01233_w_row025_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row025=true := by decide +kernel
#print axioms leaf01233_w_row025_weighted
#print axioms leaf01233_w_row025_identity
#print axioms leaf01233_w_row025_positive
def leaf01233_w_row026 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01233_w_affine)
theorem leaf01233_w_row026_weighted : leaf01233_w_row026=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row026_identity : leaf01233_w_row026=NestedInteger.coefficientFrom 88 26 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 26 0 leaf01233_w_affine leaf01233_w_row026 IntegerBernsteinWeights88.row026 (IntegerBernsteinTable.checked (n := 2) 88 26 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row026 leaf01233_w_affine_length IntegerBernsteinWeights88.row026_identity) leaf01233_w_row026_weighted
theorem leaf01233_w_row026_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row026=true := by decide +kernel
#print axioms leaf01233_w_row026_weighted
#print axioms leaf01233_w_row026_identity
#print axioms leaf01233_w_row026_positive
def leaf01233_w_row027 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01233_w_affine)
theorem leaf01233_w_row027_weighted : leaf01233_w_row027=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row027_identity : leaf01233_w_row027=NestedInteger.coefficientFrom 88 27 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 27 0 leaf01233_w_affine leaf01233_w_row027 IntegerBernsteinWeights88.row027 (IntegerBernsteinTable.checked (n := 2) 88 27 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row027 leaf01233_w_affine_length IntegerBernsteinWeights88.row027_identity) leaf01233_w_row027_weighted
theorem leaf01233_w_row027_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row027=true := by decide +kernel
#print axioms leaf01233_w_row027_weighted
#print axioms leaf01233_w_row027_identity
#print axioms leaf01233_w_row027_positive
def leaf01233_w_row028 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01233_w_affine)
theorem leaf01233_w_row028_weighted : leaf01233_w_row028=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row028_identity : leaf01233_w_row028=NestedInteger.coefficientFrom 88 28 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 28 0 leaf01233_w_affine leaf01233_w_row028 IntegerBernsteinWeights88.row028 (IntegerBernsteinTable.checked (n := 2) 88 28 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row028 leaf01233_w_affine_length IntegerBernsteinWeights88.row028_identity) leaf01233_w_row028_weighted
theorem leaf01233_w_row028_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row028=true := by decide +kernel
#print axioms leaf01233_w_row028_weighted
#print axioms leaf01233_w_row028_identity
#print axioms leaf01233_w_row028_positive
def leaf01233_w_row029 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01233_w_affine)
theorem leaf01233_w_row029_weighted : leaf01233_w_row029=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row029_identity : leaf01233_w_row029=NestedInteger.coefficientFrom 88 29 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 29 0 leaf01233_w_affine leaf01233_w_row029 IntegerBernsteinWeights88.row029 (IntegerBernsteinTable.checked (n := 2) 88 29 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row029 leaf01233_w_affine_length IntegerBernsteinWeights88.row029_identity) leaf01233_w_row029_weighted
theorem leaf01233_w_row029_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row029=true := by decide +kernel
#print axioms leaf01233_w_row029_weighted
#print axioms leaf01233_w_row029_identity
#print axioms leaf01233_w_row029_positive
def leaf01233_w_row030 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01233_w_affine)
theorem leaf01233_w_row030_weighted : leaf01233_w_row030=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row030_identity : leaf01233_w_row030=NestedInteger.coefficientFrom 88 30 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 30 0 leaf01233_w_affine leaf01233_w_row030 IntegerBernsteinWeights88.row030 (IntegerBernsteinTable.checked (n := 2) 88 30 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row030 leaf01233_w_affine_length IntegerBernsteinWeights88.row030_identity) leaf01233_w_row030_weighted
theorem leaf01233_w_row030_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row030=true := by decide +kernel
#print axioms leaf01233_w_row030_weighted
#print axioms leaf01233_w_row030_identity
#print axioms leaf01233_w_row030_positive
def leaf01233_w_row031 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01233_w_affine)
theorem leaf01233_w_row031_weighted : leaf01233_w_row031=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row031_identity : leaf01233_w_row031=NestedInteger.coefficientFrom 88 31 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 31 0 leaf01233_w_affine leaf01233_w_row031 IntegerBernsteinWeights88.row031 (IntegerBernsteinTable.checked (n := 2) 88 31 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row031 leaf01233_w_affine_length IntegerBernsteinWeights88.row031_identity) leaf01233_w_row031_weighted
theorem leaf01233_w_row031_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row031=true := by decide +kernel
#print axioms leaf01233_w_row031_weighted
#print axioms leaf01233_w_row031_identity
#print axioms leaf01233_w_row031_positive
def leaf01233_w_row032 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01233_w_affine)
theorem leaf01233_w_row032_weighted : leaf01233_w_row032=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row032_identity : leaf01233_w_row032=NestedInteger.coefficientFrom 88 32 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 32 0 leaf01233_w_affine leaf01233_w_row032 IntegerBernsteinWeights88.row032 (IntegerBernsteinTable.checked (n := 2) 88 32 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row032 leaf01233_w_affine_length IntegerBernsteinWeights88.row032_identity) leaf01233_w_row032_weighted
theorem leaf01233_w_row032_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row032=true := by decide +kernel
#print axioms leaf01233_w_row032_weighted
#print axioms leaf01233_w_row032_identity
#print axioms leaf01233_w_row032_positive
def leaf01233_w_row033 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01233_w_affine)
theorem leaf01233_w_row033_weighted : leaf01233_w_row033=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row033_identity : leaf01233_w_row033=NestedInteger.coefficientFrom 88 33 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 33 0 leaf01233_w_affine leaf01233_w_row033 IntegerBernsteinWeights88.row033 (IntegerBernsteinTable.checked (n := 2) 88 33 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row033 leaf01233_w_affine_length IntegerBernsteinWeights88.row033_identity) leaf01233_w_row033_weighted
theorem leaf01233_w_row033_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row033=true := by decide +kernel
#print axioms leaf01233_w_row033_weighted
#print axioms leaf01233_w_row033_identity
#print axioms leaf01233_w_row033_positive
def leaf01233_w_row034 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01233_w_affine)
theorem leaf01233_w_row034_weighted : leaf01233_w_row034=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row034_identity : leaf01233_w_row034=NestedInteger.coefficientFrom 88 34 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 34 0 leaf01233_w_affine leaf01233_w_row034 IntegerBernsteinWeights88.row034 (IntegerBernsteinTable.checked (n := 2) 88 34 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row034 leaf01233_w_affine_length IntegerBernsteinWeights88.row034_identity) leaf01233_w_row034_weighted
theorem leaf01233_w_row034_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row034=true := by decide +kernel
#print axioms leaf01233_w_row034_weighted
#print axioms leaf01233_w_row034_identity
#print axioms leaf01233_w_row034_positive
def leaf01233_w_row035 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01233_w_affine)
theorem leaf01233_w_row035_weighted : leaf01233_w_row035=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row035_identity : leaf01233_w_row035=NestedInteger.coefficientFrom 88 35 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 35 0 leaf01233_w_affine leaf01233_w_row035 IntegerBernsteinWeights88.row035 (IntegerBernsteinTable.checked (n := 2) 88 35 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row035 leaf01233_w_affine_length IntegerBernsteinWeights88.row035_identity) leaf01233_w_row035_weighted
theorem leaf01233_w_row035_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row035=true := by decide +kernel
#print axioms leaf01233_w_row035_weighted
#print axioms leaf01233_w_row035_identity
#print axioms leaf01233_w_row035_positive
def leaf01233_w_row036 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01233_w_affine)
theorem leaf01233_w_row036_weighted : leaf01233_w_row036=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row036_identity : leaf01233_w_row036=NestedInteger.coefficientFrom 88 36 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 36 0 leaf01233_w_affine leaf01233_w_row036 IntegerBernsteinWeights88.row036 (IntegerBernsteinTable.checked (n := 2) 88 36 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row036 leaf01233_w_affine_length IntegerBernsteinWeights88.row036_identity) leaf01233_w_row036_weighted
theorem leaf01233_w_row036_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row036=true := by decide +kernel
#print axioms leaf01233_w_row036_weighted
#print axioms leaf01233_w_row036_identity
#print axioms leaf01233_w_row036_positive
def leaf01233_w_row037 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01233_w_affine)
theorem leaf01233_w_row037_weighted : leaf01233_w_row037=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row037_identity : leaf01233_w_row037=NestedInteger.coefficientFrom 88 37 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 37 0 leaf01233_w_affine leaf01233_w_row037 IntegerBernsteinWeights88.row037 (IntegerBernsteinTable.checked (n := 2) 88 37 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row037 leaf01233_w_affine_length IntegerBernsteinWeights88.row037_identity) leaf01233_w_row037_weighted
theorem leaf01233_w_row037_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row037=true := by decide +kernel
#print axioms leaf01233_w_row037_weighted
#print axioms leaf01233_w_row037_identity
#print axioms leaf01233_w_row037_positive
def leaf01233_w_row038 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01233_w_affine)
theorem leaf01233_w_row038_weighted : leaf01233_w_row038=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row038_identity : leaf01233_w_row038=NestedInteger.coefficientFrom 88 38 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 38 0 leaf01233_w_affine leaf01233_w_row038 IntegerBernsteinWeights88.row038 (IntegerBernsteinTable.checked (n := 2) 88 38 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row038 leaf01233_w_affine_length IntegerBernsteinWeights88.row038_identity) leaf01233_w_row038_weighted
theorem leaf01233_w_row038_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row038=true := by decide +kernel
#print axioms leaf01233_w_row038_weighted
#print axioms leaf01233_w_row038_identity
#print axioms leaf01233_w_row038_positive
def leaf01233_w_row039 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01233_w_affine)
theorem leaf01233_w_row039_weighted : leaf01233_w_row039=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row039_identity : leaf01233_w_row039=NestedInteger.coefficientFrom 88 39 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 39 0 leaf01233_w_affine leaf01233_w_row039 IntegerBernsteinWeights88.row039 (IntegerBernsteinTable.checked (n := 2) 88 39 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row039 leaf01233_w_affine_length IntegerBernsteinWeights88.row039_identity) leaf01233_w_row039_weighted
theorem leaf01233_w_row039_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row039=true := by decide +kernel
#print axioms leaf01233_w_row039_weighted
#print axioms leaf01233_w_row039_identity
#print axioms leaf01233_w_row039_positive
def leaf01233_w_row040 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01233_w_affine)
theorem leaf01233_w_row040_weighted : leaf01233_w_row040=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row040_identity : leaf01233_w_row040=NestedInteger.coefficientFrom 88 40 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 40 0 leaf01233_w_affine leaf01233_w_row040 IntegerBernsteinWeights88.row040 (IntegerBernsteinTable.checked (n := 2) 88 40 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row040 leaf01233_w_affine_length IntegerBernsteinWeights88.row040_identity) leaf01233_w_row040_weighted
theorem leaf01233_w_row040_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row040=true := by decide +kernel
#print axioms leaf01233_w_row040_weighted
#print axioms leaf01233_w_row040_identity
#print axioms leaf01233_w_row040_positive
def leaf01233_w_row041 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01233_w_affine)
theorem leaf01233_w_row041_weighted : leaf01233_w_row041=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row041_identity : leaf01233_w_row041=NestedInteger.coefficientFrom 88 41 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 41 0 leaf01233_w_affine leaf01233_w_row041 IntegerBernsteinWeights88.row041 (IntegerBernsteinTable.checked (n := 2) 88 41 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row041 leaf01233_w_affine_length IntegerBernsteinWeights88.row041_identity) leaf01233_w_row041_weighted
theorem leaf01233_w_row041_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row041=true := by decide +kernel
#print axioms leaf01233_w_row041_weighted
#print axioms leaf01233_w_row041_identity
#print axioms leaf01233_w_row041_positive
def leaf01233_w_row042 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01233_w_affine)
theorem leaf01233_w_row042_weighted : leaf01233_w_row042=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row042_identity : leaf01233_w_row042=NestedInteger.coefficientFrom 88 42 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 42 0 leaf01233_w_affine leaf01233_w_row042 IntegerBernsteinWeights88.row042 (IntegerBernsteinTable.checked (n := 2) 88 42 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row042 leaf01233_w_affine_length IntegerBernsteinWeights88.row042_identity) leaf01233_w_row042_weighted
theorem leaf01233_w_row042_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row042=true := by decide +kernel
#print axioms leaf01233_w_row042_weighted
#print axioms leaf01233_w_row042_identity
#print axioms leaf01233_w_row042_positive
def leaf01233_w_row043 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01233_w_affine)
theorem leaf01233_w_row043_weighted : leaf01233_w_row043=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row043_identity : leaf01233_w_row043=NestedInteger.coefficientFrom 88 43 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 43 0 leaf01233_w_affine leaf01233_w_row043 IntegerBernsteinWeights88.row043 (IntegerBernsteinTable.checked (n := 2) 88 43 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row043 leaf01233_w_affine_length IntegerBernsteinWeights88.row043_identity) leaf01233_w_row043_weighted
theorem leaf01233_w_row043_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row043=true := by decide +kernel
#print axioms leaf01233_w_row043_weighted
#print axioms leaf01233_w_row043_identity
#print axioms leaf01233_w_row043_positive
def leaf01233_w_row044 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01233_w_affine)
theorem leaf01233_w_row044_weighted : leaf01233_w_row044=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row044_identity : leaf01233_w_row044=NestedInteger.coefficientFrom 88 44 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 44 0 leaf01233_w_affine leaf01233_w_row044 IntegerBernsteinWeights88.row044 (IntegerBernsteinTable.checked (n := 2) 88 44 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row044 leaf01233_w_affine_length IntegerBernsteinWeights88.row044_identity) leaf01233_w_row044_weighted
theorem leaf01233_w_row044_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row044=true := by decide +kernel
#print axioms leaf01233_w_row044_weighted
#print axioms leaf01233_w_row044_identity
#print axioms leaf01233_w_row044_positive
def leaf01233_w_row045 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01233_w_affine)
theorem leaf01233_w_row045_weighted : leaf01233_w_row045=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row045_identity : leaf01233_w_row045=NestedInteger.coefficientFrom 88 45 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 45 0 leaf01233_w_affine leaf01233_w_row045 IntegerBernsteinWeights88.row045 (IntegerBernsteinTable.checked (n := 2) 88 45 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row045 leaf01233_w_affine_length IntegerBernsteinWeights88.row045_identity) leaf01233_w_row045_weighted
theorem leaf01233_w_row045_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row045=true := by decide +kernel
#print axioms leaf01233_w_row045_weighted
#print axioms leaf01233_w_row045_identity
#print axioms leaf01233_w_row045_positive
def leaf01233_w_row046 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01233_w_affine)
theorem leaf01233_w_row046_weighted : leaf01233_w_row046=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row046_identity : leaf01233_w_row046=NestedInteger.coefficientFrom 88 46 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 46 0 leaf01233_w_affine leaf01233_w_row046 IntegerBernsteinWeights88.row046 (IntegerBernsteinTable.checked (n := 2) 88 46 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row046 leaf01233_w_affine_length IntegerBernsteinWeights88.row046_identity) leaf01233_w_row046_weighted
theorem leaf01233_w_row046_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row046=true := by decide +kernel
#print axioms leaf01233_w_row046_weighted
#print axioms leaf01233_w_row046_identity
#print axioms leaf01233_w_row046_positive
def leaf01233_w_row047 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01233_w_affine)
theorem leaf01233_w_row047_weighted : leaf01233_w_row047=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row047_identity : leaf01233_w_row047=NestedInteger.coefficientFrom 88 47 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 47 0 leaf01233_w_affine leaf01233_w_row047 IntegerBernsteinWeights88.row047 (IntegerBernsteinTable.checked (n := 2) 88 47 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row047 leaf01233_w_affine_length IntegerBernsteinWeights88.row047_identity) leaf01233_w_row047_weighted
theorem leaf01233_w_row047_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row047=true := by decide +kernel
#print axioms leaf01233_w_row047_weighted
#print axioms leaf01233_w_row047_identity
#print axioms leaf01233_w_row047_positive
def leaf01233_w_row048 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01233_w_affine)
theorem leaf01233_w_row048_weighted : leaf01233_w_row048=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row048_identity : leaf01233_w_row048=NestedInteger.coefficientFrom 88 48 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 48 0 leaf01233_w_affine leaf01233_w_row048 IntegerBernsteinWeights88.row048 (IntegerBernsteinTable.checked (n := 2) 88 48 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row048 leaf01233_w_affine_length IntegerBernsteinWeights88.row048_identity) leaf01233_w_row048_weighted
theorem leaf01233_w_row048_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row048=true := by decide +kernel
#print axioms leaf01233_w_row048_weighted
#print axioms leaf01233_w_row048_identity
#print axioms leaf01233_w_row048_positive
def leaf01233_w_row049 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01233_w_affine)
theorem leaf01233_w_row049_weighted : leaf01233_w_row049=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row049_identity : leaf01233_w_row049=NestedInteger.coefficientFrom 88 49 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 49 0 leaf01233_w_affine leaf01233_w_row049 IntegerBernsteinWeights88.row049 (IntegerBernsteinTable.checked (n := 2) 88 49 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row049 leaf01233_w_affine_length IntegerBernsteinWeights88.row049_identity) leaf01233_w_row049_weighted
theorem leaf01233_w_row049_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row049=true := by decide +kernel
#print axioms leaf01233_w_row049_weighted
#print axioms leaf01233_w_row049_identity
#print axioms leaf01233_w_row049_positive
def leaf01233_w_row050 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01233_w_affine)
theorem leaf01233_w_row050_weighted : leaf01233_w_row050=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row050_identity : leaf01233_w_row050=NestedInteger.coefficientFrom 88 50 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 50 0 leaf01233_w_affine leaf01233_w_row050 IntegerBernsteinWeights88.row050 (IntegerBernsteinTable.checked (n := 2) 88 50 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row050 leaf01233_w_affine_length IntegerBernsteinWeights88.row050_identity) leaf01233_w_row050_weighted
theorem leaf01233_w_row050_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row050=true := by decide +kernel
#print axioms leaf01233_w_row050_weighted
#print axioms leaf01233_w_row050_identity
#print axioms leaf01233_w_row050_positive
def leaf01233_w_row051 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01233_w_affine)
theorem leaf01233_w_row051_weighted : leaf01233_w_row051=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row051_identity : leaf01233_w_row051=NestedInteger.coefficientFrom 88 51 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 51 0 leaf01233_w_affine leaf01233_w_row051 IntegerBernsteinWeights88.row051 (IntegerBernsteinTable.checked (n := 2) 88 51 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row051 leaf01233_w_affine_length IntegerBernsteinWeights88.row051_identity) leaf01233_w_row051_weighted
theorem leaf01233_w_row051_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row051=true := by decide +kernel
#print axioms leaf01233_w_row051_weighted
#print axioms leaf01233_w_row051_identity
#print axioms leaf01233_w_row051_positive
def leaf01233_w_row052 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01233_w_affine)
theorem leaf01233_w_row052_weighted : leaf01233_w_row052=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row052_identity : leaf01233_w_row052=NestedInteger.coefficientFrom 88 52 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 52 0 leaf01233_w_affine leaf01233_w_row052 IntegerBernsteinWeights88.row052 (IntegerBernsteinTable.checked (n := 2) 88 52 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row052 leaf01233_w_affine_length IntegerBernsteinWeights88.row052_identity) leaf01233_w_row052_weighted
theorem leaf01233_w_row052_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row052=true := by decide +kernel
#print axioms leaf01233_w_row052_weighted
#print axioms leaf01233_w_row052_identity
#print axioms leaf01233_w_row052_positive
def leaf01233_w_row053 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01233_w_affine)
theorem leaf01233_w_row053_weighted : leaf01233_w_row053=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row053_identity : leaf01233_w_row053=NestedInteger.coefficientFrom 88 53 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 53 0 leaf01233_w_affine leaf01233_w_row053 IntegerBernsteinWeights88.row053 (IntegerBernsteinTable.checked (n := 2) 88 53 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row053 leaf01233_w_affine_length IntegerBernsteinWeights88.row053_identity) leaf01233_w_row053_weighted
theorem leaf01233_w_row053_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row053=true := by decide +kernel
#print axioms leaf01233_w_row053_weighted
#print axioms leaf01233_w_row053_identity
#print axioms leaf01233_w_row053_positive
def leaf01233_w_row054 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01233_w_affine)
theorem leaf01233_w_row054_weighted : leaf01233_w_row054=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row054_identity : leaf01233_w_row054=NestedInteger.coefficientFrom 88 54 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 54 0 leaf01233_w_affine leaf01233_w_row054 IntegerBernsteinWeights88.row054 (IntegerBernsteinTable.checked (n := 2) 88 54 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row054 leaf01233_w_affine_length IntegerBernsteinWeights88.row054_identity) leaf01233_w_row054_weighted
theorem leaf01233_w_row054_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row054=true := by decide +kernel
#print axioms leaf01233_w_row054_weighted
#print axioms leaf01233_w_row054_identity
#print axioms leaf01233_w_row054_positive
def leaf01233_w_row055 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01233_w_affine)
theorem leaf01233_w_row055_weighted : leaf01233_w_row055=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row055_identity : leaf01233_w_row055=NestedInteger.coefficientFrom 88 55 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 55 0 leaf01233_w_affine leaf01233_w_row055 IntegerBernsteinWeights88.row055 (IntegerBernsteinTable.checked (n := 2) 88 55 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row055 leaf01233_w_affine_length IntegerBernsteinWeights88.row055_identity) leaf01233_w_row055_weighted
theorem leaf01233_w_row055_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row055=true := by decide +kernel
#print axioms leaf01233_w_row055_weighted
#print axioms leaf01233_w_row055_identity
#print axioms leaf01233_w_row055_positive
def leaf01233_w_row056 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01233_w_affine)
theorem leaf01233_w_row056_weighted : leaf01233_w_row056=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row056_identity : leaf01233_w_row056=NestedInteger.coefficientFrom 88 56 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 56 0 leaf01233_w_affine leaf01233_w_row056 IntegerBernsteinWeights88.row056 (IntegerBernsteinTable.checked (n := 2) 88 56 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row056 leaf01233_w_affine_length IntegerBernsteinWeights88.row056_identity) leaf01233_w_row056_weighted
theorem leaf01233_w_row056_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row056=true := by decide +kernel
#print axioms leaf01233_w_row056_weighted
#print axioms leaf01233_w_row056_identity
#print axioms leaf01233_w_row056_positive
def leaf01233_w_row057 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01233_w_affine)
theorem leaf01233_w_row057_weighted : leaf01233_w_row057=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row057_identity : leaf01233_w_row057=NestedInteger.coefficientFrom 88 57 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 57 0 leaf01233_w_affine leaf01233_w_row057 IntegerBernsteinWeights88.row057 (IntegerBernsteinTable.checked (n := 2) 88 57 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row057 leaf01233_w_affine_length IntegerBernsteinWeights88.row057_identity) leaf01233_w_row057_weighted
theorem leaf01233_w_row057_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row057=true := by decide +kernel
#print axioms leaf01233_w_row057_weighted
#print axioms leaf01233_w_row057_identity
#print axioms leaf01233_w_row057_positive
def leaf01233_w_row058 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01233_w_affine)
theorem leaf01233_w_row058_weighted : leaf01233_w_row058=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row058_identity : leaf01233_w_row058=NestedInteger.coefficientFrom 88 58 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 58 0 leaf01233_w_affine leaf01233_w_row058 IntegerBernsteinWeights88.row058 (IntegerBernsteinTable.checked (n := 2) 88 58 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row058 leaf01233_w_affine_length IntegerBernsteinWeights88.row058_identity) leaf01233_w_row058_weighted
theorem leaf01233_w_row058_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row058=true := by decide +kernel
#print axioms leaf01233_w_row058_weighted
#print axioms leaf01233_w_row058_identity
#print axioms leaf01233_w_row058_positive
def leaf01233_w_row059 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01233_w_affine)
theorem leaf01233_w_row059_weighted : leaf01233_w_row059=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row059_identity : leaf01233_w_row059=NestedInteger.coefficientFrom 88 59 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 59 0 leaf01233_w_affine leaf01233_w_row059 IntegerBernsteinWeights88.row059 (IntegerBernsteinTable.checked (n := 2) 88 59 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row059 leaf01233_w_affine_length IntegerBernsteinWeights88.row059_identity) leaf01233_w_row059_weighted
theorem leaf01233_w_row059_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row059=true := by decide +kernel
#print axioms leaf01233_w_row059_weighted
#print axioms leaf01233_w_row059_identity
#print axioms leaf01233_w_row059_positive
def leaf01233_w_row060 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01233_w_affine)
theorem leaf01233_w_row060_weighted : leaf01233_w_row060=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row060_identity : leaf01233_w_row060=NestedInteger.coefficientFrom 88 60 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 60 0 leaf01233_w_affine leaf01233_w_row060 IntegerBernsteinWeights88.row060 (IntegerBernsteinTable.checked (n := 2) 88 60 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row060 leaf01233_w_affine_length IntegerBernsteinWeights88.row060_identity) leaf01233_w_row060_weighted
theorem leaf01233_w_row060_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row060=true := by decide +kernel
#print axioms leaf01233_w_row060_weighted
#print axioms leaf01233_w_row060_identity
#print axioms leaf01233_w_row060_positive
def leaf01233_w_row061 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01233_w_affine)
theorem leaf01233_w_row061_weighted : leaf01233_w_row061=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row061_identity : leaf01233_w_row061=NestedInteger.coefficientFrom 88 61 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 61 0 leaf01233_w_affine leaf01233_w_row061 IntegerBernsteinWeights88.row061 (IntegerBernsteinTable.checked (n := 2) 88 61 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row061 leaf01233_w_affine_length IntegerBernsteinWeights88.row061_identity) leaf01233_w_row061_weighted
theorem leaf01233_w_row061_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row061=true := by decide +kernel
#print axioms leaf01233_w_row061_weighted
#print axioms leaf01233_w_row061_identity
#print axioms leaf01233_w_row061_positive
def leaf01233_w_row062 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01233_w_affine)
theorem leaf01233_w_row062_weighted : leaf01233_w_row062=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row062_identity : leaf01233_w_row062=NestedInteger.coefficientFrom 88 62 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 62 0 leaf01233_w_affine leaf01233_w_row062 IntegerBernsteinWeights88.row062 (IntegerBernsteinTable.checked (n := 2) 88 62 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row062 leaf01233_w_affine_length IntegerBernsteinWeights88.row062_identity) leaf01233_w_row062_weighted
theorem leaf01233_w_row062_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row062=true := by decide +kernel
#print axioms leaf01233_w_row062_weighted
#print axioms leaf01233_w_row062_identity
#print axioms leaf01233_w_row062_positive
def leaf01233_w_row063 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01233_w_affine)
theorem leaf01233_w_row063_weighted : leaf01233_w_row063=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row063_identity : leaf01233_w_row063=NestedInteger.coefficientFrom 88 63 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 63 0 leaf01233_w_affine leaf01233_w_row063 IntegerBernsteinWeights88.row063 (IntegerBernsteinTable.checked (n := 2) 88 63 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row063 leaf01233_w_affine_length IntegerBernsteinWeights88.row063_identity) leaf01233_w_row063_weighted
theorem leaf01233_w_row063_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row063=true := by decide +kernel
#print axioms leaf01233_w_row063_weighted
#print axioms leaf01233_w_row063_identity
#print axioms leaf01233_w_row063_positive
def leaf01233_w_row064 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01233_w_affine)
theorem leaf01233_w_row064_weighted : leaf01233_w_row064=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row064_identity : leaf01233_w_row064=NestedInteger.coefficientFrom 88 64 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 64 0 leaf01233_w_affine leaf01233_w_row064 IntegerBernsteinWeights88.row064 (IntegerBernsteinTable.checked (n := 2) 88 64 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row064 leaf01233_w_affine_length IntegerBernsteinWeights88.row064_identity) leaf01233_w_row064_weighted
theorem leaf01233_w_row064_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row064=true := by decide +kernel
#print axioms leaf01233_w_row064_weighted
#print axioms leaf01233_w_row064_identity
#print axioms leaf01233_w_row064_positive
def leaf01233_w_row065 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01233_w_affine)
theorem leaf01233_w_row065_weighted : leaf01233_w_row065=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row065_identity : leaf01233_w_row065=NestedInteger.coefficientFrom 88 65 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 65 0 leaf01233_w_affine leaf01233_w_row065 IntegerBernsteinWeights88.row065 (IntegerBernsteinTable.checked (n := 2) 88 65 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row065 leaf01233_w_affine_length IntegerBernsteinWeights88.row065_identity) leaf01233_w_row065_weighted
theorem leaf01233_w_row065_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row065=true := by decide +kernel
#print axioms leaf01233_w_row065_weighted
#print axioms leaf01233_w_row065_identity
#print axioms leaf01233_w_row065_positive
def leaf01233_w_row066 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01233_w_affine)
theorem leaf01233_w_row066_weighted : leaf01233_w_row066=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row066_identity : leaf01233_w_row066=NestedInteger.coefficientFrom 88 66 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 66 0 leaf01233_w_affine leaf01233_w_row066 IntegerBernsteinWeights88.row066 (IntegerBernsteinTable.checked (n := 2) 88 66 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row066 leaf01233_w_affine_length IntegerBernsteinWeights88.row066_identity) leaf01233_w_row066_weighted
theorem leaf01233_w_row066_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row066=true := by decide +kernel
#print axioms leaf01233_w_row066_weighted
#print axioms leaf01233_w_row066_identity
#print axioms leaf01233_w_row066_positive
def leaf01233_w_row067 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01233_w_affine)
theorem leaf01233_w_row067_weighted : leaf01233_w_row067=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row067_identity : leaf01233_w_row067=NestedInteger.coefficientFrom 88 67 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 67 0 leaf01233_w_affine leaf01233_w_row067 IntegerBernsteinWeights88.row067 (IntegerBernsteinTable.checked (n := 2) 88 67 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row067 leaf01233_w_affine_length IntegerBernsteinWeights88.row067_identity) leaf01233_w_row067_weighted
theorem leaf01233_w_row067_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row067=true := by decide +kernel
#print axioms leaf01233_w_row067_weighted
#print axioms leaf01233_w_row067_identity
#print axioms leaf01233_w_row067_positive
def leaf01233_w_row068 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01233_w_affine)
theorem leaf01233_w_row068_weighted : leaf01233_w_row068=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row068_identity : leaf01233_w_row068=NestedInteger.coefficientFrom 88 68 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 68 0 leaf01233_w_affine leaf01233_w_row068 IntegerBernsteinWeights88.row068 (IntegerBernsteinTable.checked (n := 2) 88 68 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row068 leaf01233_w_affine_length IntegerBernsteinWeights88.row068_identity) leaf01233_w_row068_weighted
theorem leaf01233_w_row068_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row068=true := by decide +kernel
#print axioms leaf01233_w_row068_weighted
#print axioms leaf01233_w_row068_identity
#print axioms leaf01233_w_row068_positive
def leaf01233_w_row069 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row069 leaf01233_w_affine)
theorem leaf01233_w_row069_weighted : leaf01233_w_row069=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row069 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row069_identity : leaf01233_w_row069=NestedInteger.coefficientFrom 88 69 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 69 0 leaf01233_w_affine leaf01233_w_row069 IntegerBernsteinWeights88.row069 (IntegerBernsteinTable.checked (n := 2) 88 69 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row069 leaf01233_w_affine_length IntegerBernsteinWeights88.row069_identity) leaf01233_w_row069_weighted
theorem leaf01233_w_row069_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row069=true := by decide +kernel
#print axioms leaf01233_w_row069_weighted
#print axioms leaf01233_w_row069_identity
#print axioms leaf01233_w_row069_positive
def leaf01233_w_row070 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01233_w_affine)
theorem leaf01233_w_row070_weighted : leaf01233_w_row070=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row070_identity : leaf01233_w_row070=NestedInteger.coefficientFrom 88 70 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 70 0 leaf01233_w_affine leaf01233_w_row070 IntegerBernsteinWeights88.row070 (IntegerBernsteinTable.checked (n := 2) 88 70 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row070 leaf01233_w_affine_length IntegerBernsteinWeights88.row070_identity) leaf01233_w_row070_weighted
theorem leaf01233_w_row070_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row070=true := by decide +kernel
#print axioms leaf01233_w_row070_weighted
#print axioms leaf01233_w_row070_identity
#print axioms leaf01233_w_row070_positive
def leaf01233_w_row071 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row071 leaf01233_w_affine)
theorem leaf01233_w_row071_weighted : leaf01233_w_row071=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row071 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row071_identity : leaf01233_w_row071=NestedInteger.coefficientFrom 88 71 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 71 0 leaf01233_w_affine leaf01233_w_row071 IntegerBernsteinWeights88.row071 (IntegerBernsteinTable.checked (n := 2) 88 71 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row071 leaf01233_w_affine_length IntegerBernsteinWeights88.row071_identity) leaf01233_w_row071_weighted
theorem leaf01233_w_row071_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row071=true := by decide +kernel
#print axioms leaf01233_w_row071_weighted
#print axioms leaf01233_w_row071_identity
#print axioms leaf01233_w_row071_positive
def leaf01233_w_row072 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01233_w_affine)
theorem leaf01233_w_row072_weighted : leaf01233_w_row072=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row072_identity : leaf01233_w_row072=NestedInteger.coefficientFrom 88 72 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 72 0 leaf01233_w_affine leaf01233_w_row072 IntegerBernsteinWeights88.row072 (IntegerBernsteinTable.checked (n := 2) 88 72 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row072 leaf01233_w_affine_length IntegerBernsteinWeights88.row072_identity) leaf01233_w_row072_weighted
theorem leaf01233_w_row072_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row072=true := by decide +kernel
#print axioms leaf01233_w_row072_weighted
#print axioms leaf01233_w_row072_identity
#print axioms leaf01233_w_row072_positive
def leaf01233_w_row073 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row073 leaf01233_w_affine)
theorem leaf01233_w_row073_weighted : leaf01233_w_row073=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row073 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row073_identity : leaf01233_w_row073=NestedInteger.coefficientFrom 88 73 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 73 0 leaf01233_w_affine leaf01233_w_row073 IntegerBernsteinWeights88.row073 (IntegerBernsteinTable.checked (n := 2) 88 73 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row073 leaf01233_w_affine_length IntegerBernsteinWeights88.row073_identity) leaf01233_w_row073_weighted
theorem leaf01233_w_row073_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row073=true := by decide +kernel
#print axioms leaf01233_w_row073_weighted
#print axioms leaf01233_w_row073_identity
#print axioms leaf01233_w_row073_positive
def leaf01233_w_row074 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row074 leaf01233_w_affine)
theorem leaf01233_w_row074_weighted : leaf01233_w_row074=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row074 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row074_identity : leaf01233_w_row074=NestedInteger.coefficientFrom 88 74 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 74 0 leaf01233_w_affine leaf01233_w_row074 IntegerBernsteinWeights88.row074 (IntegerBernsteinTable.checked (n := 2) 88 74 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row074 leaf01233_w_affine_length IntegerBernsteinWeights88.row074_identity) leaf01233_w_row074_weighted
theorem leaf01233_w_row074_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row074=true := by decide +kernel
#print axioms leaf01233_w_row074_weighted
#print axioms leaf01233_w_row074_identity
#print axioms leaf01233_w_row074_positive
def leaf01233_w_row075 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01233_w_affine)
theorem leaf01233_w_row075_weighted : leaf01233_w_row075=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row075_identity : leaf01233_w_row075=NestedInteger.coefficientFrom 88 75 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 75 0 leaf01233_w_affine leaf01233_w_row075 IntegerBernsteinWeights88.row075 (IntegerBernsteinTable.checked (n := 2) 88 75 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row075 leaf01233_w_affine_length IntegerBernsteinWeights88.row075_identity) leaf01233_w_row075_weighted
theorem leaf01233_w_row075_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row075=true := by decide +kernel
#print axioms leaf01233_w_row075_weighted
#print axioms leaf01233_w_row075_identity
#print axioms leaf01233_w_row075_positive
def leaf01233_w_row076 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01233_w_affine)
theorem leaf01233_w_row076_weighted : leaf01233_w_row076=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row076_identity : leaf01233_w_row076=NestedInteger.coefficientFrom 88 76 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 76 0 leaf01233_w_affine leaf01233_w_row076 IntegerBernsteinWeights88.row076 (IntegerBernsteinTable.checked (n := 2) 88 76 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row076 leaf01233_w_affine_length IntegerBernsteinWeights88.row076_identity) leaf01233_w_row076_weighted
theorem leaf01233_w_row076_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row076=true := by decide +kernel
#print axioms leaf01233_w_row076_weighted
#print axioms leaf01233_w_row076_identity
#print axioms leaf01233_w_row076_positive
def leaf01233_w_row077 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row077 leaf01233_w_affine)
theorem leaf01233_w_row077_weighted : leaf01233_w_row077=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row077 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row077_identity : leaf01233_w_row077=NestedInteger.coefficientFrom 88 77 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 77 0 leaf01233_w_affine leaf01233_w_row077 IntegerBernsteinWeights88.row077 (IntegerBernsteinTable.checked (n := 2) 88 77 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row077 leaf01233_w_affine_length IntegerBernsteinWeights88.row077_identity) leaf01233_w_row077_weighted
theorem leaf01233_w_row077_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row077=true := by decide +kernel
#print axioms leaf01233_w_row077_weighted
#print axioms leaf01233_w_row077_identity
#print axioms leaf01233_w_row077_positive
def leaf01233_w_row078 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row078 leaf01233_w_affine)
theorem leaf01233_w_row078_weighted : leaf01233_w_row078=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row078 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row078_identity : leaf01233_w_row078=NestedInteger.coefficientFrom 88 78 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 78 0 leaf01233_w_affine leaf01233_w_row078 IntegerBernsteinWeights88.row078 (IntegerBernsteinTable.checked (n := 2) 88 78 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row078 leaf01233_w_affine_length IntegerBernsteinWeights88.row078_identity) leaf01233_w_row078_weighted
theorem leaf01233_w_row078_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row078=true := by decide +kernel
#print axioms leaf01233_w_row078_weighted
#print axioms leaf01233_w_row078_identity
#print axioms leaf01233_w_row078_positive
def leaf01233_w_row079 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01233_w_affine)
theorem leaf01233_w_row079_weighted : leaf01233_w_row079=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row079_identity : leaf01233_w_row079=NestedInteger.coefficientFrom 88 79 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 79 0 leaf01233_w_affine leaf01233_w_row079 IntegerBernsteinWeights88.row079 (IntegerBernsteinTable.checked (n := 2) 88 79 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row079 leaf01233_w_affine_length IntegerBernsteinWeights88.row079_identity) leaf01233_w_row079_weighted
theorem leaf01233_w_row079_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row079=true := by decide +kernel
#print axioms leaf01233_w_row079_weighted
#print axioms leaf01233_w_row079_identity
#print axioms leaf01233_w_row079_positive
def leaf01233_w_row080 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01233_w_affine)
theorem leaf01233_w_row080_weighted : leaf01233_w_row080=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row080_identity : leaf01233_w_row080=NestedInteger.coefficientFrom 88 80 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 80 0 leaf01233_w_affine leaf01233_w_row080 IntegerBernsteinWeights88.row080 (IntegerBernsteinTable.checked (n := 2) 88 80 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row080 leaf01233_w_affine_length IntegerBernsteinWeights88.row080_identity) leaf01233_w_row080_weighted
theorem leaf01233_w_row080_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row080=true := by decide +kernel
#print axioms leaf01233_w_row080_weighted
#print axioms leaf01233_w_row080_identity
#print axioms leaf01233_w_row080_positive
def leaf01233_w_row081 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01233_w_affine)
theorem leaf01233_w_row081_weighted : leaf01233_w_row081=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row081_identity : leaf01233_w_row081=NestedInteger.coefficientFrom 88 81 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 81 0 leaf01233_w_affine leaf01233_w_row081 IntegerBernsteinWeights88.row081 (IntegerBernsteinTable.checked (n := 2) 88 81 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row081 leaf01233_w_affine_length IntegerBernsteinWeights88.row081_identity) leaf01233_w_row081_weighted
theorem leaf01233_w_row081_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row081=true := by decide +kernel
#print axioms leaf01233_w_row081_weighted
#print axioms leaf01233_w_row081_identity
#print axioms leaf01233_w_row081_positive
def leaf01233_w_row082 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf01233_w_affine)
theorem leaf01233_w_row082_weighted : leaf01233_w_row082=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row082_identity : leaf01233_w_row082=NestedInteger.coefficientFrom 88 82 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 82 0 leaf01233_w_affine leaf01233_w_row082 IntegerBernsteinWeights88.row082 (IntegerBernsteinTable.checked (n := 2) 88 82 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row082 leaf01233_w_affine_length IntegerBernsteinWeights88.row082_identity) leaf01233_w_row082_weighted
theorem leaf01233_w_row082_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row082=true := by decide +kernel
#print axioms leaf01233_w_row082_weighted
#print axioms leaf01233_w_row082_identity
#print axioms leaf01233_w_row082_positive
def leaf01233_w_row083 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01233_w_affine)
theorem leaf01233_w_row083_weighted : leaf01233_w_row083=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row083_identity : leaf01233_w_row083=NestedInteger.coefficientFrom 88 83 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 83 0 leaf01233_w_affine leaf01233_w_row083 IntegerBernsteinWeights88.row083 (IntegerBernsteinTable.checked (n := 2) 88 83 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row083 leaf01233_w_affine_length IntegerBernsteinWeights88.row083_identity) leaf01233_w_row083_weighted
theorem leaf01233_w_row083_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row083=true := by decide +kernel
#print axioms leaf01233_w_row083_weighted
#print axioms leaf01233_w_row083_identity
#print axioms leaf01233_w_row083_positive
def leaf01233_w_row084 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01233_w_affine)
theorem leaf01233_w_row084_weighted : leaf01233_w_row084=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row084_identity : leaf01233_w_row084=NestedInteger.coefficientFrom 88 84 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 84 0 leaf01233_w_affine leaf01233_w_row084 IntegerBernsteinWeights88.row084 (IntegerBernsteinTable.checked (n := 2) 88 84 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row084 leaf01233_w_affine_length IntegerBernsteinWeights88.row084_identity) leaf01233_w_row084_weighted
theorem leaf01233_w_row084_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row084=true := by decide +kernel
#print axioms leaf01233_w_row084_weighted
#print axioms leaf01233_w_row084_identity
#print axioms leaf01233_w_row084_positive
def leaf01233_w_row085 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row085 leaf01233_w_affine)
theorem leaf01233_w_row085_weighted : leaf01233_w_row085=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row085 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row085_identity : leaf01233_w_row085=NestedInteger.coefficientFrom 88 85 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 85 0 leaf01233_w_affine leaf01233_w_row085 IntegerBernsteinWeights88.row085 (IntegerBernsteinTable.checked (n := 2) 88 85 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row085 leaf01233_w_affine_length IntegerBernsteinWeights88.row085_identity) leaf01233_w_row085_weighted
theorem leaf01233_w_row085_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row085=true := by decide +kernel
#print axioms leaf01233_w_row085_weighted
#print axioms leaf01233_w_row085_identity
#print axioms leaf01233_w_row085_positive
def leaf01233_w_row086 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01233_w_affine)
theorem leaf01233_w_row086_weighted : leaf01233_w_row086=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row086_identity : leaf01233_w_row086=NestedInteger.coefficientFrom 88 86 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 86 0 leaf01233_w_affine leaf01233_w_row086 IntegerBernsteinWeights88.row086 (IntegerBernsteinTable.checked (n := 2) 88 86 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row086 leaf01233_w_affine_length IntegerBernsteinWeights88.row086_identity) leaf01233_w_row086_weighted
theorem leaf01233_w_row086_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row086=true := by decide +kernel
#print axioms leaf01233_w_row086_weighted
#print axioms leaf01233_w_row086_identity
#print axioms leaf01233_w_row086_positive
def leaf01233_w_row087 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01233_w_affine)
theorem leaf01233_w_row087_weighted : leaf01233_w_row087=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row087_identity : leaf01233_w_row087=NestedInteger.coefficientFrom 88 87 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 87 0 leaf01233_w_affine leaf01233_w_row087 IntegerBernsteinWeights88.row087 (IntegerBernsteinTable.checked (n := 2) 88 87 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row087 leaf01233_w_affine_length IntegerBernsteinWeights88.row087_identity) leaf01233_w_row087_weighted
theorem leaf01233_w_row087_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row087=true := by decide +kernel
#print axioms leaf01233_w_row087_weighted
#print axioms leaf01233_w_row087_identity
#print axioms leaf01233_w_row087_positive
def leaf01233_w_row088 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01233_w_affine)
theorem leaf01233_w_row088_weighted : leaf01233_w_row088=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01233_w_affine := by decide +kernel
theorem leaf01233_w_row088_identity : leaf01233_w_row088=NestedInteger.coefficientFrom 88 88 0 leaf01233_w_affine :=
  IntegerWeightedBernstein.checked 88 88 0 leaf01233_w_affine leaf01233_w_row088 IntegerBernsteinWeights88.row088 (IntegerBernsteinTable.checked (n := 2) 88 88 0 89 leaf01233_w_affine IntegerBernsteinWeights88.row088 leaf01233_w_affine_length IntegerBernsteinWeights88.row088_identity) leaf01233_w_row088_weighted
theorem leaf01233_w_row088_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01233_w_row088=true := by decide +kernel
#print axioms leaf01233_w_row088_weighted
#print axioms leaf01233_w_row088_identity
#print axioms leaf01233_w_row088_positive
def leaf01233_w_rows : Fin 89 → NestedInteger.Poly 2 := ![leaf01233_w_row000,leaf01233_w_row001,leaf01233_w_row002,leaf01233_w_row003,leaf01233_w_row004,leaf01233_w_row005,leaf01233_w_row006,leaf01233_w_row007,leaf01233_w_row008,leaf01233_w_row009,leaf01233_w_row010,leaf01233_w_row011,leaf01233_w_row012,leaf01233_w_row013,leaf01233_w_row014,leaf01233_w_row015,leaf01233_w_row016,leaf01233_w_row017,leaf01233_w_row018,leaf01233_w_row019,leaf01233_w_row020,leaf01233_w_row021,leaf01233_w_row022,leaf01233_w_row023,leaf01233_w_row024,leaf01233_w_row025,leaf01233_w_row026,leaf01233_w_row027,leaf01233_w_row028,leaf01233_w_row029,leaf01233_w_row030,leaf01233_w_row031,leaf01233_w_row032,leaf01233_w_row033,leaf01233_w_row034,leaf01233_w_row035,leaf01233_w_row036,leaf01233_w_row037,leaf01233_w_row038,leaf01233_w_row039,leaf01233_w_row040,leaf01233_w_row041,leaf01233_w_row042,leaf01233_w_row043,leaf01233_w_row044,leaf01233_w_row045,leaf01233_w_row046,leaf01233_w_row047,leaf01233_w_row048,leaf01233_w_row049,leaf01233_w_row050,leaf01233_w_row051,leaf01233_w_row052,leaf01233_w_row053,leaf01233_w_row054,leaf01233_w_row055,leaf01233_w_row056,leaf01233_w_row057,leaf01233_w_row058,leaf01233_w_row059,leaf01233_w_row060,leaf01233_w_row061,leaf01233_w_row062,leaf01233_w_row063,leaf01233_w_row064,leaf01233_w_row065,leaf01233_w_row066,leaf01233_w_row067,leaf01233_w_row068,leaf01233_w_row069,leaf01233_w_row070,leaf01233_w_row071,leaf01233_w_row072,leaf01233_w_row073,leaf01233_w_row074,leaf01233_w_row075,leaf01233_w_row076,leaf01233_w_row077,leaf01233_w_row078,leaf01233_w_row079,leaf01233_w_row080,leaf01233_w_row081,leaf01233_w_row082,leaf01233_w_row083,leaf01233_w_row084,leaf01233_w_row085,leaf01233_w_row086,leaf01233_w_row087,leaf01233_w_row088]
theorem leaf01233_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf01233_w_affine=true := by
  apply IntegerBernsteinRows.checked ![88,4,4] leaf01233_w_affine leaf01233_w_rows (by decide +kernel)
  · intro j
    fin_cases j
    · exact leaf01233_w_row000_identity
    · exact leaf01233_w_row001_identity
    · exact leaf01233_w_row002_identity
    · exact leaf01233_w_row003_identity
    · exact leaf01233_w_row004_identity
    · exact leaf01233_w_row005_identity
    · exact leaf01233_w_row006_identity
    · exact leaf01233_w_row007_identity
    · exact leaf01233_w_row008_identity
    · exact leaf01233_w_row009_identity
    · exact leaf01233_w_row010_identity
    · exact leaf01233_w_row011_identity
    · exact leaf01233_w_row012_identity
    · exact leaf01233_w_row013_identity
    · exact leaf01233_w_row014_identity
    · exact leaf01233_w_row015_identity
    · exact leaf01233_w_row016_identity
    · exact leaf01233_w_row017_identity
    · exact leaf01233_w_row018_identity
    · exact leaf01233_w_row019_identity
    · exact leaf01233_w_row020_identity
    · exact leaf01233_w_row021_identity
    · exact leaf01233_w_row022_identity
    · exact leaf01233_w_row023_identity
    · exact leaf01233_w_row024_identity
    · exact leaf01233_w_row025_identity
    · exact leaf01233_w_row026_identity
    · exact leaf01233_w_row027_identity
    · exact leaf01233_w_row028_identity
    · exact leaf01233_w_row029_identity
    · exact leaf01233_w_row030_identity
    · exact leaf01233_w_row031_identity
    · exact leaf01233_w_row032_identity
    · exact leaf01233_w_row033_identity
    · exact leaf01233_w_row034_identity
    · exact leaf01233_w_row035_identity
    · exact leaf01233_w_row036_identity
    · exact leaf01233_w_row037_identity
    · exact leaf01233_w_row038_identity
    · exact leaf01233_w_row039_identity
    · exact leaf01233_w_row040_identity
    · exact leaf01233_w_row041_identity
    · exact leaf01233_w_row042_identity
    · exact leaf01233_w_row043_identity
    · exact leaf01233_w_row044_identity
    · exact leaf01233_w_row045_identity
    · exact leaf01233_w_row046_identity
    · exact leaf01233_w_row047_identity
    · exact leaf01233_w_row048_identity
    · exact leaf01233_w_row049_identity
    · exact leaf01233_w_row050_identity
    · exact leaf01233_w_row051_identity
    · exact leaf01233_w_row052_identity
    · exact leaf01233_w_row053_identity
    · exact leaf01233_w_row054_identity
    · exact leaf01233_w_row055_identity
    · exact leaf01233_w_row056_identity
    · exact leaf01233_w_row057_identity
    · exact leaf01233_w_row058_identity
    · exact leaf01233_w_row059_identity
    · exact leaf01233_w_row060_identity
    · exact leaf01233_w_row061_identity
    · exact leaf01233_w_row062_identity
    · exact leaf01233_w_row063_identity
    · exact leaf01233_w_row064_identity
    · exact leaf01233_w_row065_identity
    · exact leaf01233_w_row066_identity
    · exact leaf01233_w_row067_identity
    · exact leaf01233_w_row068_identity
    · exact leaf01233_w_row069_identity
    · exact leaf01233_w_row070_identity
    · exact leaf01233_w_row071_identity
    · exact leaf01233_w_row072_identity
    · exact leaf01233_w_row073_identity
    · exact leaf01233_w_row074_identity
    · exact leaf01233_w_row075_identity
    · exact leaf01233_w_row076_identity
    · exact leaf01233_w_row077_identity
    · exact leaf01233_w_row078_identity
    · exact leaf01233_w_row079_identity
    · exact leaf01233_w_row080_identity
    · exact leaf01233_w_row081_identity
    · exact leaf01233_w_row082_identity
    · exact leaf01233_w_row083_identity
    · exact leaf01233_w_row084_identity
    · exact leaf01233_w_row085_identity
    · exact leaf01233_w_row086_identity
    · exact leaf01233_w_row087_identity
    · exact leaf01233_w_row088_identity
  · intro j
    fin_cases j
    · exact leaf01233_w_row000_positive
    · exact leaf01233_w_row001_positive
    · exact leaf01233_w_row002_positive
    · exact leaf01233_w_row003_positive
    · exact leaf01233_w_row004_positive
    · exact leaf01233_w_row005_positive
    · exact leaf01233_w_row006_positive
    · exact leaf01233_w_row007_positive
    · exact leaf01233_w_row008_positive
    · exact leaf01233_w_row009_positive
    · exact leaf01233_w_row010_positive
    · exact leaf01233_w_row011_positive
    · exact leaf01233_w_row012_positive
    · exact leaf01233_w_row013_positive
    · exact leaf01233_w_row014_positive
    · exact leaf01233_w_row015_positive
    · exact leaf01233_w_row016_positive
    · exact leaf01233_w_row017_positive
    · exact leaf01233_w_row018_positive
    · exact leaf01233_w_row019_positive
    · exact leaf01233_w_row020_positive
    · exact leaf01233_w_row021_positive
    · exact leaf01233_w_row022_positive
    · exact leaf01233_w_row023_positive
    · exact leaf01233_w_row024_positive
    · exact leaf01233_w_row025_positive
    · exact leaf01233_w_row026_positive
    · exact leaf01233_w_row027_positive
    · exact leaf01233_w_row028_positive
    · exact leaf01233_w_row029_positive
    · exact leaf01233_w_row030_positive
    · exact leaf01233_w_row031_positive
    · exact leaf01233_w_row032_positive
    · exact leaf01233_w_row033_positive
    · exact leaf01233_w_row034_positive
    · exact leaf01233_w_row035_positive
    · exact leaf01233_w_row036_positive
    · exact leaf01233_w_row037_positive
    · exact leaf01233_w_row038_positive
    · exact leaf01233_w_row039_positive
    · exact leaf01233_w_row040_positive
    · exact leaf01233_w_row041_positive
    · exact leaf01233_w_row042_positive
    · exact leaf01233_w_row043_positive
    · exact leaf01233_w_row044_positive
    · exact leaf01233_w_row045_positive
    · exact leaf01233_w_row046_positive
    · exact leaf01233_w_row047_positive
    · exact leaf01233_w_row048_positive
    · exact leaf01233_w_row049_positive
    · exact leaf01233_w_row050_positive
    · exact leaf01233_w_row051_positive
    · exact leaf01233_w_row052_positive
    · exact leaf01233_w_row053_positive
    · exact leaf01233_w_row054_positive
    · exact leaf01233_w_row055_positive
    · exact leaf01233_w_row056_positive
    · exact leaf01233_w_row057_positive
    · exact leaf01233_w_row058_positive
    · exact leaf01233_w_row059_positive
    · exact leaf01233_w_row060_positive
    · exact leaf01233_w_row061_positive
    · exact leaf01233_w_row062_positive
    · exact leaf01233_w_row063_positive
    · exact leaf01233_w_row064_positive
    · exact leaf01233_w_row065_positive
    · exact leaf01233_w_row066_positive
    · exact leaf01233_w_row067_positive
    · exact leaf01233_w_row068_positive
    · exact leaf01233_w_row069_positive
    · exact leaf01233_w_row070_positive
    · exact leaf01233_w_row071_positive
    · exact leaf01233_w_row072_positive
    · exact leaf01233_w_row073_positive
    · exact leaf01233_w_row074_positive
    · exact leaf01233_w_row075_positive
    · exact leaf01233_w_row076_positive
    · exact leaf01233_w_row077_positive
    · exact leaf01233_w_row078_positive
    · exact leaf01233_w_row079_positive
    · exact leaf01233_w_row080_positive
    · exact leaf01233_w_row081_positive
    · exact leaf01233_w_row082_positive
    · exact leaf01233_w_row083_positive
    · exact leaf01233_w_row084_positive
    · exact leaf01233_w_row085_positive
    · exact leaf01233_w_row086_positive
    · exact leaf01233_w_row087_positive
    · exact leaf01233_w_row088_positive
#print axioms leaf01233_sign
theorem leaf01233_log : RationalLog.accepts (1282090889/1073741824) (380840489/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01233_log
def leaf01233 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack00.pack true (28410533977/500000000000) (1282090889/1073741824) (380840489/4294967296) 0 8 ![88,4,4] ![(5/8),(31/32),(15/16)] ![(1/8),(1/32),(1/32)] 15252789286638977024000000000000 ![8,32,32] leaf01233_w_affine
theorem leaf01233_checked : FastNestedCellData.accepts 1 4 4 leaf01233=true :=
  IntegerPiecewiseCell.accepts_make DegreeOneIntegerNorm00.pack true (28410533977/500000000000) (1282090889/1073741824) (380840489/4294967296) 0 8 ![88,4,4] ![(5/8),(31/32),(15/16)] ![(1/8),(1/32),(1/32)]
    15252789286638977024000000000000 19247293864772152925562772684281 338735165631768317776500000000000 ![5,31,30] ![1,1,1] ![8,32,32] leaf01233_w_raw leaf01233_w_inner leaf01233_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01233_raw leaf01233_rectangular leaf01233_inner leaf01233_w_affine_eval leaf01233_sign leaf01233_log
#print axioms leaf01233_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
