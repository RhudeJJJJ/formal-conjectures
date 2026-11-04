/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01667Outer07

/-!
# Original leaf 01667 — Affine

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01667.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01667_w_suffix07 : NestedInteger.Poly 3 := leaf01667_w_piece07
theorem leaf01667_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 84 leaf01667_w_source07)) x := by
  have h : leaf01667_w_segment07=leaf01667_w_source07 := by decide +kernel
  rw [leaf01667_w_suffix07,leaf01667_w_piece07_identity,h]
#print axioms leaf01667_w_suffix07_eval
def leaf01667_w_suffix06 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source07.length) leaf01667_w_piece06) leaf01667_w_suffix07)
theorem leaf01667_w_suffix06_join : leaf01667_w_suffix06=NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source07.length) leaf01667_w_piece06) leaf01667_w_suffix07 := by decide +kernel
theorem leaf01667_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 72 leaf01667_w_source06)) x := by
  have hlen : leaf01667_w_segment06.length=12 := by decide +kernel
  calc
    _ = (128 : ℝ)^leaf01667_w_source07.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 72 leaf01667_w_segment06)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 (72+leaf01667_w_segment06.length) leaf01667_w_source07)) x := by
      rw [leaf01667_w_suffix06_join,cast_add,eval_add,cast_scale,eval_scale,leaf01667_w_piece06_identity,leaf01667_w_suffix07_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 72 (leaf01667_w_segment06++leaf01667_w_source07))) x :=
      (IntegerOuterPieces.eval_append 12 1 128 72 leaf01667_w_segment06 leaf01667_w_source07 x).symm
    _ = _ := by rw [show leaf01667_w_segment06++leaf01667_w_source07=leaf01667_w_source06 from List.take_append_drop 12 leaf01667_w_source06]
#print axioms leaf01667_w_suffix06_join
#print axioms leaf01667_w_suffix06_eval
def leaf01667_w_suffix05 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source06.length) leaf01667_w_piece05) leaf01667_w_suffix06)
theorem leaf01667_w_suffix05_join : leaf01667_w_suffix05=NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source06.length) leaf01667_w_piece05) leaf01667_w_suffix06 := by decide +kernel
theorem leaf01667_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 60 leaf01667_w_source05)) x := by
  have hlen : leaf01667_w_segment05.length=12 := by decide +kernel
  calc
    _ = (128 : ℝ)^leaf01667_w_source06.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 60 leaf01667_w_segment05)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 (60+leaf01667_w_segment05.length) leaf01667_w_source06)) x := by
      rw [leaf01667_w_suffix05_join,cast_add,eval_add,cast_scale,eval_scale,leaf01667_w_piece05_identity,leaf01667_w_suffix06_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 60 (leaf01667_w_segment05++leaf01667_w_source06))) x :=
      (IntegerOuterPieces.eval_append 12 1 128 60 leaf01667_w_segment05 leaf01667_w_source06 x).symm
    _ = _ := by rw [show leaf01667_w_segment05++leaf01667_w_source06=leaf01667_w_source05 from List.take_append_drop 12 leaf01667_w_source05]
#print axioms leaf01667_w_suffix05_join
#print axioms leaf01667_w_suffix05_eval
def leaf01667_w_suffix04 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source05.length) leaf01667_w_piece04) leaf01667_w_suffix05)
theorem leaf01667_w_suffix04_join : leaf01667_w_suffix04=NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source05.length) leaf01667_w_piece04) leaf01667_w_suffix05 := by decide +kernel
theorem leaf01667_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 48 leaf01667_w_source04)) x := by
  have hlen : leaf01667_w_segment04.length=12 := by decide +kernel
  calc
    _ = (128 : ℝ)^leaf01667_w_source05.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 48 leaf01667_w_segment04)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 (48+leaf01667_w_segment04.length) leaf01667_w_source05)) x := by
      rw [leaf01667_w_suffix04_join,cast_add,eval_add,cast_scale,eval_scale,leaf01667_w_piece04_identity,leaf01667_w_suffix05_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 48 (leaf01667_w_segment04++leaf01667_w_source05))) x :=
      (IntegerOuterPieces.eval_append 12 1 128 48 leaf01667_w_segment04 leaf01667_w_source05 x).symm
    _ = _ := by rw [show leaf01667_w_segment04++leaf01667_w_source05=leaf01667_w_source04 from List.take_append_drop 12 leaf01667_w_source04]
#print axioms leaf01667_w_suffix04_join
#print axioms leaf01667_w_suffix04_eval
def leaf01667_w_suffix03 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source04.length) leaf01667_w_piece03) leaf01667_w_suffix04)
theorem leaf01667_w_suffix03_join : leaf01667_w_suffix03=NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source04.length) leaf01667_w_piece03) leaf01667_w_suffix04 := by decide +kernel
theorem leaf01667_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 36 leaf01667_w_source03)) x := by
  have hlen : leaf01667_w_segment03.length=12 := by decide +kernel
  calc
    _ = (128 : ℝ)^leaf01667_w_source04.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 36 leaf01667_w_segment03)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 (36+leaf01667_w_segment03.length) leaf01667_w_source04)) x := by
      rw [leaf01667_w_suffix03_join,cast_add,eval_add,cast_scale,eval_scale,leaf01667_w_piece03_identity,leaf01667_w_suffix04_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 36 (leaf01667_w_segment03++leaf01667_w_source04))) x :=
      (IntegerOuterPieces.eval_append 12 1 128 36 leaf01667_w_segment03 leaf01667_w_source04 x).symm
    _ = _ := by rw [show leaf01667_w_segment03++leaf01667_w_source04=leaf01667_w_source03 from List.take_append_drop 12 leaf01667_w_source03]
#print axioms leaf01667_w_suffix03_join
#print axioms leaf01667_w_suffix03_eval
def leaf01667_w_suffix02 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source03.length) leaf01667_w_piece02) leaf01667_w_suffix03)
theorem leaf01667_w_suffix02_join : leaf01667_w_suffix02=NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source03.length) leaf01667_w_piece02) leaf01667_w_suffix03 := by decide +kernel
theorem leaf01667_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 24 leaf01667_w_source02)) x := by
  have hlen : leaf01667_w_segment02.length=12 := by decide +kernel
  calc
    _ = (128 : ℝ)^leaf01667_w_source03.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 24 leaf01667_w_segment02)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 (24+leaf01667_w_segment02.length) leaf01667_w_source03)) x := by
      rw [leaf01667_w_suffix02_join,cast_add,eval_add,cast_scale,eval_scale,leaf01667_w_piece02_identity,leaf01667_w_suffix03_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 24 (leaf01667_w_segment02++leaf01667_w_source03))) x :=
      (IntegerOuterPieces.eval_append 12 1 128 24 leaf01667_w_segment02 leaf01667_w_source03 x).symm
    _ = _ := by rw [show leaf01667_w_segment02++leaf01667_w_source03=leaf01667_w_source02 from List.take_append_drop 12 leaf01667_w_source02]
#print axioms leaf01667_w_suffix02_join
#print axioms leaf01667_w_suffix02_eval
def leaf01667_w_suffix01 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source02.length) leaf01667_w_piece01) leaf01667_w_suffix02)
theorem leaf01667_w_suffix01_join : leaf01667_w_suffix01=NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source02.length) leaf01667_w_piece01) leaf01667_w_suffix02 := by decide +kernel
theorem leaf01667_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 12 leaf01667_w_source01)) x := by
  have hlen : leaf01667_w_segment01.length=12 := by decide +kernel
  calc
    _ = (128 : ℝ)^leaf01667_w_source02.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 12 leaf01667_w_segment01)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 (12+leaf01667_w_segment01.length) leaf01667_w_source02)) x := by
      rw [leaf01667_w_suffix01_join,cast_add,eval_add,cast_scale,eval_scale,leaf01667_w_piece01_identity,leaf01667_w_suffix02_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 12 (leaf01667_w_segment01++leaf01667_w_source02))) x :=
      (IntegerOuterPieces.eval_append 12 1 128 12 leaf01667_w_segment01 leaf01667_w_source02 x).symm
    _ = _ := by rw [show leaf01667_w_segment01++leaf01667_w_source02=leaf01667_w_source01 from List.take_append_drop 12 leaf01667_w_source01]
#print axioms leaf01667_w_suffix01_join
#print axioms leaf01667_w_suffix01_eval
def leaf01667_w_affine : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source01.length) leaf01667_w_piece00) leaf01667_w_suffix01)
theorem leaf01667_w_affine_join : leaf01667_w_affine=NestedInteger.add (NestedInteger.scale (128^leaf01667_w_source01.length) leaf01667_w_piece00) leaf01667_w_suffix01 := by decide +kernel
theorem leaf01667_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01667_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 0 leaf01667_w_source00)) x := by
  have hlen : leaf01667_w_segment00.length=12 := by decide +kernel
  calc
    _ = (128 : ℝ)^leaf01667_w_source01.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 0 leaf01667_w_segment00)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 (0+leaf01667_w_segment00.length) leaf01667_w_source01)) x := by
      rw [leaf01667_w_affine_join,cast_add,eval_add,cast_scale,eval_scale,leaf01667_w_piece00_identity,leaf01667_w_suffix01_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 12 1 128 0 (leaf01667_w_segment00++leaf01667_w_source01))) x :=
      (IntegerOuterPieces.eval_append 12 1 128 0 leaf01667_w_segment00 leaf01667_w_source01 x).symm
    _ = _ := by rw [show leaf01667_w_segment00++leaf01667_w_source01=leaf01667_w_source00 from List.take_append_drop 12 leaf01667_w_source00]
#print axioms leaf01667_w_affine_join
#print axioms leaf01667_w_affine_eval
theorem leaf01667_w_affine_length : leaf01667_w_affine.length=89 := by decide +kernel
#print axioms leaf01667_w_affine_length
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
