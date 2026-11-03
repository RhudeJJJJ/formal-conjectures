/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01370Base

/-!
# Weighted outer transformation for leaf 01370

These declarations retain the original polynomial data and proof bodies.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01370.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01370_w_source00 : NestedInteger.Poly 3 := leaf01370_w_inner
def leaf01370_w_segment00 : NestedInteger.Poly 3 := leaf01370_w_source00.take 12
def leaf01370_w_weights00 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 0 leaf01370_w_segment00)
theorem leaf01370_w_weights00_identity : leaf01370_w_weights00=IntegerWeightedOuter.weights 10 1 32 0 leaf01370_w_segment00 := by decide +kernel
def leaf01370_w_piece00 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights00 leaf01370_w_segment00)
theorem leaf01370_w_piece00_weighted : leaf01370_w_piece00=IntegerWeightedOuter.applyWeights leaf01370_w_weights00 leaf01370_w_segment00 := by decide +kernel
theorem leaf01370_w_piece00_identity : leaf01370_w_piece00=IntegerOuterTerms.transform 10 1 32 0 leaf01370_w_segment00 :=
  IntegerWeightedOuter.checked 10 1 32 0 leaf01370_w_segment00 leaf01370_w_piece00 leaf01370_w_weights00 leaf01370_w_weights00_identity leaf01370_w_piece00_weighted
#print axioms leaf01370_w_weights00_identity
#print axioms leaf01370_w_piece00_weighted
#print axioms leaf01370_w_piece00_identity
def leaf01370_w_source01 : NestedInteger.Poly 3 := leaf01370_w_source00.drop 12
def leaf01370_w_segment01 : NestedInteger.Poly 3 := leaf01370_w_source01.take 12
def leaf01370_w_weights01 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 12 leaf01370_w_segment01)
theorem leaf01370_w_weights01_identity : leaf01370_w_weights01=IntegerWeightedOuter.weights 10 1 32 12 leaf01370_w_segment01 := by decide +kernel
def leaf01370_w_piece01 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights01 leaf01370_w_segment01)
theorem leaf01370_w_piece01_weighted : leaf01370_w_piece01=IntegerWeightedOuter.applyWeights leaf01370_w_weights01 leaf01370_w_segment01 := by decide +kernel
theorem leaf01370_w_piece01_identity : leaf01370_w_piece01=IntegerOuterTerms.transform 10 1 32 12 leaf01370_w_segment01 :=
  IntegerWeightedOuter.checked 10 1 32 12 leaf01370_w_segment01 leaf01370_w_piece01 leaf01370_w_weights01 leaf01370_w_weights01_identity leaf01370_w_piece01_weighted
#print axioms leaf01370_w_weights01_identity
#print axioms leaf01370_w_piece01_weighted
#print axioms leaf01370_w_piece01_identity
def leaf01370_w_source02 : NestedInteger.Poly 3 := leaf01370_w_source01.drop 12
def leaf01370_w_segment02 : NestedInteger.Poly 3 := leaf01370_w_source02.take 12
def leaf01370_w_weights02 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 24 leaf01370_w_segment02)
theorem leaf01370_w_weights02_identity : leaf01370_w_weights02=IntegerWeightedOuter.weights 10 1 32 24 leaf01370_w_segment02 := by decide +kernel
def leaf01370_w_piece02 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights02 leaf01370_w_segment02)
theorem leaf01370_w_piece02_weighted : leaf01370_w_piece02=IntegerWeightedOuter.applyWeights leaf01370_w_weights02 leaf01370_w_segment02 := by decide +kernel
theorem leaf01370_w_piece02_identity : leaf01370_w_piece02=IntegerOuterTerms.transform 10 1 32 24 leaf01370_w_segment02 :=
  IntegerWeightedOuter.checked 10 1 32 24 leaf01370_w_segment02 leaf01370_w_piece02 leaf01370_w_weights02 leaf01370_w_weights02_identity leaf01370_w_piece02_weighted
#print axioms leaf01370_w_weights02_identity
#print axioms leaf01370_w_piece02_weighted
#print axioms leaf01370_w_piece02_identity
def leaf01370_w_source03 : NestedInteger.Poly 3 := leaf01370_w_source02.drop 12
def leaf01370_w_segment03 : NestedInteger.Poly 3 := leaf01370_w_source03.take 12
def leaf01370_w_weights03 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 36 leaf01370_w_segment03)
theorem leaf01370_w_weights03_identity : leaf01370_w_weights03=IntegerWeightedOuter.weights 10 1 32 36 leaf01370_w_segment03 := by decide +kernel
def leaf01370_w_piece03 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights03 leaf01370_w_segment03)
theorem leaf01370_w_piece03_weighted : leaf01370_w_piece03=IntegerWeightedOuter.applyWeights leaf01370_w_weights03 leaf01370_w_segment03 := by decide +kernel
theorem leaf01370_w_piece03_identity : leaf01370_w_piece03=IntegerOuterTerms.transform 10 1 32 36 leaf01370_w_segment03 :=
  IntegerWeightedOuter.checked 10 1 32 36 leaf01370_w_segment03 leaf01370_w_piece03 leaf01370_w_weights03 leaf01370_w_weights03_identity leaf01370_w_piece03_weighted
#print axioms leaf01370_w_weights03_identity
#print axioms leaf01370_w_piece03_weighted
#print axioms leaf01370_w_piece03_identity
def leaf01370_w_source04 : NestedInteger.Poly 3 := leaf01370_w_source03.drop 12
def leaf01370_w_segment04 : NestedInteger.Poly 3 := leaf01370_w_source04.take 12
def leaf01370_w_weights04 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 48 leaf01370_w_segment04)
theorem leaf01370_w_weights04_identity : leaf01370_w_weights04=IntegerWeightedOuter.weights 10 1 32 48 leaf01370_w_segment04 := by decide +kernel
def leaf01370_w_piece04 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights04 leaf01370_w_segment04)
theorem leaf01370_w_piece04_weighted : leaf01370_w_piece04=IntegerWeightedOuter.applyWeights leaf01370_w_weights04 leaf01370_w_segment04 := by decide +kernel
theorem leaf01370_w_piece04_identity : leaf01370_w_piece04=IntegerOuterTerms.transform 10 1 32 48 leaf01370_w_segment04 :=
  IntegerWeightedOuter.checked 10 1 32 48 leaf01370_w_segment04 leaf01370_w_piece04 leaf01370_w_weights04 leaf01370_w_weights04_identity leaf01370_w_piece04_weighted
#print axioms leaf01370_w_weights04_identity
#print axioms leaf01370_w_piece04_weighted
#print axioms leaf01370_w_piece04_identity
def leaf01370_w_source05 : NestedInteger.Poly 3 := leaf01370_w_source04.drop 12
def leaf01370_w_segment05 : NestedInteger.Poly 3 := leaf01370_w_source05.take 12
def leaf01370_w_weights05 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 60 leaf01370_w_segment05)
theorem leaf01370_w_weights05_identity : leaf01370_w_weights05=IntegerWeightedOuter.weights 10 1 32 60 leaf01370_w_segment05 := by decide +kernel
def leaf01370_w_piece05 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights05 leaf01370_w_segment05)
theorem leaf01370_w_piece05_weighted : leaf01370_w_piece05=IntegerWeightedOuter.applyWeights leaf01370_w_weights05 leaf01370_w_segment05 := by decide +kernel
theorem leaf01370_w_piece05_identity : leaf01370_w_piece05=IntegerOuterTerms.transform 10 1 32 60 leaf01370_w_segment05 :=
  IntegerWeightedOuter.checked 10 1 32 60 leaf01370_w_segment05 leaf01370_w_piece05 leaf01370_w_weights05 leaf01370_w_weights05_identity leaf01370_w_piece05_weighted
#print axioms leaf01370_w_weights05_identity
#print axioms leaf01370_w_piece05_weighted
#print axioms leaf01370_w_piece05_identity
def leaf01370_w_source06 : NestedInteger.Poly 3 := leaf01370_w_source05.drop 12
def leaf01370_w_segment06 : NestedInteger.Poly 3 := leaf01370_w_source06.take 12
def leaf01370_w_weights06 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 72 leaf01370_w_segment06)
theorem leaf01370_w_weights06_identity : leaf01370_w_weights06=IntegerWeightedOuter.weights 10 1 32 72 leaf01370_w_segment06 := by decide +kernel
def leaf01370_w_piece06 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights06 leaf01370_w_segment06)
theorem leaf01370_w_piece06_weighted : leaf01370_w_piece06=IntegerWeightedOuter.applyWeights leaf01370_w_weights06 leaf01370_w_segment06 := by decide +kernel
theorem leaf01370_w_piece06_identity : leaf01370_w_piece06=IntegerOuterTerms.transform 10 1 32 72 leaf01370_w_segment06 :=
  IntegerWeightedOuter.checked 10 1 32 72 leaf01370_w_segment06 leaf01370_w_piece06 leaf01370_w_weights06 leaf01370_w_weights06_identity leaf01370_w_piece06_weighted
#print axioms leaf01370_w_weights06_identity
#print axioms leaf01370_w_piece06_weighted
#print axioms leaf01370_w_piece06_identity
def leaf01370_w_source07 : NestedInteger.Poly 3 := leaf01370_w_source06.drop 12
def leaf01370_w_segment07 : NestedInteger.Poly 3 := leaf01370_w_source07.take 12
def leaf01370_w_weights07 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 10 1 32 84 leaf01370_w_segment07)
theorem leaf01370_w_weights07_identity : leaf01370_w_weights07=IntegerWeightedOuter.weights 10 1 32 84 leaf01370_w_segment07 := by decide +kernel
def leaf01370_w_piece07 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01370_w_weights07 leaf01370_w_segment07)
theorem leaf01370_w_piece07_weighted : leaf01370_w_piece07=IntegerWeightedOuter.applyWeights leaf01370_w_weights07 leaf01370_w_segment07 := by decide +kernel
theorem leaf01370_w_piece07_identity : leaf01370_w_piece07=IntegerOuterTerms.transform 10 1 32 84 leaf01370_w_segment07 :=
  IntegerWeightedOuter.checked 10 1 32 84 leaf01370_w_segment07 leaf01370_w_piece07 leaf01370_w_weights07 leaf01370_w_weights07_identity leaf01370_w_piece07_weighted
#print axioms leaf01370_w_weights07_identity
#print axioms leaf01370_w_piece07_weighted
#print axioms leaf01370_w_piece07_identity
def leaf01370_w_suffix07 : NestedInteger.Poly 3 := leaf01370_w_piece07
theorem leaf01370_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 84 leaf01370_w_source07)) x := by
  have h : leaf01370_w_segment07=leaf01370_w_source07 := by decide +kernel
  rw [leaf01370_w_suffix07,leaf01370_w_piece07_identity,h]
#print axioms leaf01370_w_suffix07_eval
def leaf01370_w_suffix06 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source07.length) leaf01370_w_piece06) leaf01370_w_suffix07)
theorem leaf01370_w_suffix06_join : leaf01370_w_suffix06=NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source07.length) leaf01370_w_piece06) leaf01370_w_suffix07 := by decide +kernel
theorem leaf01370_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 72 leaf01370_w_source06)) x := by
  have hlen : leaf01370_w_segment06.length=12 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01370_w_source07.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 72 leaf01370_w_segment06)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 (72+leaf01370_w_segment06.length) leaf01370_w_source07)) x := by
      rw [leaf01370_w_suffix06_join,cast_add,eval_add,cast_scale,eval_scale,leaf01370_w_piece06_identity,leaf01370_w_suffix07_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 72 (leaf01370_w_segment06++leaf01370_w_source07))) x :=
      (IntegerOuterPieces.eval_append 10 1 32 72 leaf01370_w_segment06 leaf01370_w_source07 x).symm
    _ = _ := by rw [show leaf01370_w_segment06++leaf01370_w_source07=leaf01370_w_source06 from List.take_append_drop 12 leaf01370_w_source06]
#print axioms leaf01370_w_suffix06_join
#print axioms leaf01370_w_suffix06_eval
def leaf01370_w_suffix05 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source06.length) leaf01370_w_piece05) leaf01370_w_suffix06)
theorem leaf01370_w_suffix05_join : leaf01370_w_suffix05=NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source06.length) leaf01370_w_piece05) leaf01370_w_suffix06 := by decide +kernel
theorem leaf01370_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 60 leaf01370_w_source05)) x := by
  have hlen : leaf01370_w_segment05.length=12 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01370_w_source06.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 60 leaf01370_w_segment05)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 (60+leaf01370_w_segment05.length) leaf01370_w_source06)) x := by
      rw [leaf01370_w_suffix05_join,cast_add,eval_add,cast_scale,eval_scale,leaf01370_w_piece05_identity,leaf01370_w_suffix06_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 60 (leaf01370_w_segment05++leaf01370_w_source06))) x :=
      (IntegerOuterPieces.eval_append 10 1 32 60 leaf01370_w_segment05 leaf01370_w_source06 x).symm
    _ = _ := by rw [show leaf01370_w_segment05++leaf01370_w_source06=leaf01370_w_source05 from List.take_append_drop 12 leaf01370_w_source05]
#print axioms leaf01370_w_suffix05_join
#print axioms leaf01370_w_suffix05_eval
def leaf01370_w_suffix04 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source05.length) leaf01370_w_piece04) leaf01370_w_suffix05)
theorem leaf01370_w_suffix04_join : leaf01370_w_suffix04=NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source05.length) leaf01370_w_piece04) leaf01370_w_suffix05 := by decide +kernel
theorem leaf01370_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 48 leaf01370_w_source04)) x := by
  have hlen : leaf01370_w_segment04.length=12 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01370_w_source05.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 48 leaf01370_w_segment04)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 (48+leaf01370_w_segment04.length) leaf01370_w_source05)) x := by
      rw [leaf01370_w_suffix04_join,cast_add,eval_add,cast_scale,eval_scale,leaf01370_w_piece04_identity,leaf01370_w_suffix05_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 48 (leaf01370_w_segment04++leaf01370_w_source05))) x :=
      (IntegerOuterPieces.eval_append 10 1 32 48 leaf01370_w_segment04 leaf01370_w_source05 x).symm
    _ = _ := by rw [show leaf01370_w_segment04++leaf01370_w_source05=leaf01370_w_source04 from List.take_append_drop 12 leaf01370_w_source04]
#print axioms leaf01370_w_suffix04_join
#print axioms leaf01370_w_suffix04_eval
def leaf01370_w_suffix03 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source04.length) leaf01370_w_piece03) leaf01370_w_suffix04)
theorem leaf01370_w_suffix03_join : leaf01370_w_suffix03=NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source04.length) leaf01370_w_piece03) leaf01370_w_suffix04 := by decide +kernel
theorem leaf01370_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 36 leaf01370_w_source03)) x := by
  have hlen : leaf01370_w_segment03.length=12 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01370_w_source04.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 36 leaf01370_w_segment03)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 (36+leaf01370_w_segment03.length) leaf01370_w_source04)) x := by
      rw [leaf01370_w_suffix03_join,cast_add,eval_add,cast_scale,eval_scale,leaf01370_w_piece03_identity,leaf01370_w_suffix04_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 36 (leaf01370_w_segment03++leaf01370_w_source04))) x :=
      (IntegerOuterPieces.eval_append 10 1 32 36 leaf01370_w_segment03 leaf01370_w_source04 x).symm
    _ = _ := by rw [show leaf01370_w_segment03++leaf01370_w_source04=leaf01370_w_source03 from List.take_append_drop 12 leaf01370_w_source03]
#print axioms leaf01370_w_suffix03_join
#print axioms leaf01370_w_suffix03_eval
def leaf01370_w_suffix02 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source03.length) leaf01370_w_piece02) leaf01370_w_suffix03)
theorem leaf01370_w_suffix02_join : leaf01370_w_suffix02=NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source03.length) leaf01370_w_piece02) leaf01370_w_suffix03 := by decide +kernel
theorem leaf01370_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 24 leaf01370_w_source02)) x := by
  have hlen : leaf01370_w_segment02.length=12 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01370_w_source03.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 24 leaf01370_w_segment02)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 (24+leaf01370_w_segment02.length) leaf01370_w_source03)) x := by
      rw [leaf01370_w_suffix02_join,cast_add,eval_add,cast_scale,eval_scale,leaf01370_w_piece02_identity,leaf01370_w_suffix03_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 24 (leaf01370_w_segment02++leaf01370_w_source03))) x :=
      (IntegerOuterPieces.eval_append 10 1 32 24 leaf01370_w_segment02 leaf01370_w_source03 x).symm
    _ = _ := by rw [show leaf01370_w_segment02++leaf01370_w_source03=leaf01370_w_source02 from List.take_append_drop 12 leaf01370_w_source02]
#print axioms leaf01370_w_suffix02_join
#print axioms leaf01370_w_suffix02_eval
def leaf01370_w_suffix01 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source02.length) leaf01370_w_piece01) leaf01370_w_suffix02)
theorem leaf01370_w_suffix01_join : leaf01370_w_suffix01=NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source02.length) leaf01370_w_piece01) leaf01370_w_suffix02 := by decide +kernel
theorem leaf01370_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 12 leaf01370_w_source01)) x := by
  have hlen : leaf01370_w_segment01.length=12 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01370_w_source02.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 12 leaf01370_w_segment01)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 (12+leaf01370_w_segment01.length) leaf01370_w_source02)) x := by
      rw [leaf01370_w_suffix01_join,cast_add,eval_add,cast_scale,eval_scale,leaf01370_w_piece01_identity,leaf01370_w_suffix02_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 12 (leaf01370_w_segment01++leaf01370_w_source02))) x :=
      (IntegerOuterPieces.eval_append 10 1 32 12 leaf01370_w_segment01 leaf01370_w_source02 x).symm
    _ = _ := by rw [show leaf01370_w_segment01++leaf01370_w_source02=leaf01370_w_source01 from List.take_append_drop 12 leaf01370_w_source01]
#print axioms leaf01370_w_suffix01_join
#print axioms leaf01370_w_suffix01_eval
def leaf01370_w_affine : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source01.length) leaf01370_w_piece00) leaf01370_w_suffix01)
theorem leaf01370_w_affine_join : leaf01370_w_affine=NestedInteger.add (NestedInteger.scale (32^leaf01370_w_source01.length) leaf01370_w_piece00) leaf01370_w_suffix01 := by decide +kernel
theorem leaf01370_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01370_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 0 leaf01370_w_source00)) x := by
  have hlen : leaf01370_w_segment00.length=12 := by decide +kernel
  calc
    _ = (32 : ℝ)^leaf01370_w_source01.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 0 leaf01370_w_segment00)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 (0+leaf01370_w_segment00.length) leaf01370_w_source01)) x := by
      rw [leaf01370_w_affine_join,cast_add,eval_add,cast_scale,eval_scale,leaf01370_w_piece00_identity,leaf01370_w_suffix01_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 10 1 32 0 (leaf01370_w_segment00++leaf01370_w_source01))) x :=
      (IntegerOuterPieces.eval_append 10 1 32 0 leaf01370_w_segment00 leaf01370_w_source01 x).symm
    _ = _ := by rw [show leaf01370_w_segment00++leaf01370_w_source01=leaf01370_w_source00 from List.take_append_drop 12 leaf01370_w_source00]
#print axioms leaf01370_w_affine_join
#print axioms leaf01370_w_affine_eval
theorem leaf01370_w_affine_length : leaf01370_w_affine.length=89 := by decide +kernel
#print axioms leaf01370_w_affine_length
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
