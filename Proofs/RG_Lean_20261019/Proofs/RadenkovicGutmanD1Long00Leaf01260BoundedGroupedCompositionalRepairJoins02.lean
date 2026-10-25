/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairPieces00
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairJoins01
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix09 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source10.length) leaf01260_w_piece09) leaf01260_w_suffix10)
theorem leaf01260_w_suffix09_join : leaf01260_w_suffix09=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source10.length) leaf01260_w_piece09) leaf01260_w_suffix10 := by decide +kernel
theorem leaf01260_w_suffix09_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix09) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 27 leaf01260_w_source09)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 27 30
    leaf01260_w_segment09 leaf01260_w_source10 leaf01260_w_source09
    leaf01260_w_piece09 leaf01260_w_suffix10 leaf01260_w_suffix09
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source09)
    leaf01260_w_piece09_identity leaf01260_w_suffix10_eval leaf01260_w_suffix09_join x
#print axioms leaf01260_w_suffix09_join
#print axioms leaf01260_w_suffix09_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix08 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source09.length) leaf01260_w_piece08) leaf01260_w_suffix09)
theorem leaf01260_w_suffix08_join : leaf01260_w_suffix08=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source09.length) leaf01260_w_piece08) leaf01260_w_suffix09 := by decide +kernel
theorem leaf01260_w_suffix08_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix08) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 24 leaf01260_w_source08)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 24 27
    leaf01260_w_segment08 leaf01260_w_source09 leaf01260_w_source08
    leaf01260_w_piece08 leaf01260_w_suffix09 leaf01260_w_suffix08
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source08)
    leaf01260_w_piece08_identity leaf01260_w_suffix09_eval leaf01260_w_suffix08_join x
#print axioms leaf01260_w_suffix08_join
#print axioms leaf01260_w_suffix08_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix07 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source08.length) leaf01260_w_piece07) leaf01260_w_suffix08)
theorem leaf01260_w_suffix07_join : leaf01260_w_suffix07=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source08.length) leaf01260_w_piece07) leaf01260_w_suffix08 := by decide +kernel
theorem leaf01260_w_suffix07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix07) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 leaf01260_w_source07)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 21 24
    leaf01260_w_segment07 leaf01260_w_source08 leaf01260_w_source07
    leaf01260_w_piece07 leaf01260_w_suffix08 leaf01260_w_suffix07
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source07)
    leaf01260_w_piece07_identity leaf01260_w_suffix08_eval leaf01260_w_suffix07_join x
#print axioms leaf01260_w_suffix07_join
#print axioms leaf01260_w_suffix07_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix06 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source07.length) leaf01260_w_piece06) leaf01260_w_suffix07)
theorem leaf01260_w_suffix06_join : leaf01260_w_suffix06=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source07.length) leaf01260_w_piece06) leaf01260_w_suffix07 := by decide +kernel
theorem leaf01260_w_suffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix06) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 18 leaf01260_w_source06)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 18 21
    leaf01260_w_segment06 leaf01260_w_source07 leaf01260_w_source06
    leaf01260_w_piece06 leaf01260_w_suffix07 leaf01260_w_suffix06
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source06)
    leaf01260_w_piece06_identity leaf01260_w_suffix07_eval leaf01260_w_suffix06_join x
#print axioms leaf01260_w_suffix06_join
#print axioms leaf01260_w_suffix06_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix05 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source06.length) leaf01260_w_piece05) leaf01260_w_suffix06)
theorem leaf01260_w_suffix05_join : leaf01260_w_suffix05=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source06.length) leaf01260_w_piece05) leaf01260_w_suffix06 := by decide +kernel
theorem leaf01260_w_suffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix05) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 15 leaf01260_w_source05)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 15 18
    leaf01260_w_segment05 leaf01260_w_source06 leaf01260_w_source05
    leaf01260_w_piece05 leaf01260_w_suffix06 leaf01260_w_suffix05
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source05)
    leaf01260_w_piece05_identity leaf01260_w_suffix06_eval leaf01260_w_suffix05_join x
#print axioms leaf01260_w_suffix05_join
#print axioms leaf01260_w_suffix05_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix04 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source05.length) leaf01260_w_piece04) leaf01260_w_suffix05)
theorem leaf01260_w_suffix04_join : leaf01260_w_suffix04=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source05.length) leaf01260_w_piece04) leaf01260_w_suffix05 := by decide +kernel
theorem leaf01260_w_suffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix04) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 12 leaf01260_w_source04)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 12 15
    leaf01260_w_segment04 leaf01260_w_source05 leaf01260_w_source04
    leaf01260_w_piece04 leaf01260_w_suffix05 leaf01260_w_suffix04
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source04)
    leaf01260_w_piece04_identity leaf01260_w_suffix05_eval leaf01260_w_suffix04_join x
#print axioms leaf01260_w_suffix04_join
#print axioms leaf01260_w_suffix04_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix03 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source04.length) leaf01260_w_piece03) leaf01260_w_suffix04)
theorem leaf01260_w_suffix03_join : leaf01260_w_suffix03=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source04.length) leaf01260_w_piece03) leaf01260_w_suffix04 := by decide +kernel
theorem leaf01260_w_suffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix03) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_source03)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 9 12
    leaf01260_w_segment03 leaf01260_w_source04 leaf01260_w_source03
    leaf01260_w_piece03 leaf01260_w_suffix04 leaf01260_w_suffix03
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source03)
    leaf01260_w_piece03_identity leaf01260_w_suffix04_eval leaf01260_w_suffix03_join x
#print axioms leaf01260_w_suffix03_join
#print axioms leaf01260_w_suffix03_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix02 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source03.length) leaf01260_w_piece02) leaf01260_w_suffix03)
theorem leaf01260_w_suffix02_join : leaf01260_w_suffix02=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source03.length) leaf01260_w_piece02) leaf01260_w_suffix03 := by decide +kernel
theorem leaf01260_w_suffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix02) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 6 leaf01260_w_source02)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 6 9
    leaf01260_w_segment02 leaf01260_w_source03 leaf01260_w_source02
    leaf01260_w_piece02 leaf01260_w_suffix03 leaf01260_w_suffix02
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source02)
    leaf01260_w_piece02_identity leaf01260_w_suffix03_eval leaf01260_w_suffix02_join x
#print axioms leaf01260_w_suffix02_join
#print axioms leaf01260_w_suffix02_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix01 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source02.length) leaf01260_w_piece01) leaf01260_w_suffix02)
theorem leaf01260_w_suffix01_join : leaf01260_w_suffix01=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source02.length) leaf01260_w_piece01) leaf01260_w_suffix02 := by decide +kernel
theorem leaf01260_w_suffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix01) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 3 leaf01260_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 3 6
    leaf01260_w_segment01 leaf01260_w_source02 leaf01260_w_source01
    leaf01260_w_piece01 leaf01260_w_suffix02 leaf01260_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source01)
    leaf01260_w_piece01_identity leaf01260_w_suffix02_eval leaf01260_w_suffix01_join x
#print axioms leaf01260_w_suffix01_join
#print axioms leaf01260_w_suffix01_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_affine : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source01.length) leaf01260_w_piece00) leaf01260_w_suffix01)
theorem leaf01260_w_affine_join : leaf01260_w_affine=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source01.length) leaf01260_w_piece00) leaf01260_w_suffix01 := by decide +kernel
theorem leaf01260_w_affine_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_affine) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 0 3
    leaf01260_w_segment00 leaf01260_w_source01 leaf01260_w_source00
    leaf01260_w_piece00 leaf01260_w_suffix01 leaf01260_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source00)
    leaf01260_w_piece00_identity leaf01260_w_suffix01_eval leaf01260_w_affine_join x
#print axioms leaf01260_w_affine_join
#print axioms leaf01260_w_affine_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem leaf01260_w_affine_length : leaf01260_w_affine.length=89 := by decide +kernel
#print axioms leaf01260_w_affine_length
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
