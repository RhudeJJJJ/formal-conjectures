/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairPieces02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix29 : NestedInteger.Poly 3 := leaf01260_w_piece29
theorem leaf01260_w_suffix29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix29) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 87 leaf01260_w_source29)) x := by
  have h : leaf01260_w_segment29=leaf01260_w_source29 := by decide +kernel
  rw [leaf01260_w_suffix29,leaf01260_w_piece29_identity,h]
#print axioms leaf01260_w_suffix29_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix28 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source29.length) leaf01260_w_piece28) leaf01260_w_suffix29)
theorem leaf01260_w_suffix28_join : leaf01260_w_suffix28=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source29.length) leaf01260_w_piece28) leaf01260_w_suffix29 := by decide +kernel
theorem leaf01260_w_suffix28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix28) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_source28)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 84 87
    leaf01260_w_segment28 leaf01260_w_source29 leaf01260_w_source28
    leaf01260_w_piece28 leaf01260_w_suffix29 leaf01260_w_suffix28
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source28)
    leaf01260_w_piece28_identity leaf01260_w_suffix29_eval leaf01260_w_suffix28_join x
#print axioms leaf01260_w_suffix28_join
#print axioms leaf01260_w_suffix28_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix27 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source28.length) leaf01260_w_piece27) leaf01260_w_suffix28)
theorem leaf01260_w_suffix27_join : leaf01260_w_suffix27=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source28.length) leaf01260_w_piece27) leaf01260_w_suffix28 := by decide +kernel
theorem leaf01260_w_suffix27_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix27) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 81 84
    leaf01260_w_segment27 leaf01260_w_source28 leaf01260_w_source27
    leaf01260_w_piece27 leaf01260_w_suffix28 leaf01260_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source27)
    leaf01260_w_piece27_identity leaf01260_w_suffix28_eval leaf01260_w_suffix27_join x
#print axioms leaf01260_w_suffix27_join
#print axioms leaf01260_w_suffix27_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix26 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source27.length) leaf01260_w_piece26) leaf01260_w_suffix27)
theorem leaf01260_w_suffix26_join : leaf01260_w_suffix26=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source27.length) leaf01260_w_piece26) leaf01260_w_suffix27 := by decide +kernel
theorem leaf01260_w_suffix26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix26) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 leaf01260_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 78 81
    leaf01260_w_segment26 leaf01260_w_source27 leaf01260_w_source26
    leaf01260_w_piece26 leaf01260_w_suffix27 leaf01260_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source26)
    leaf01260_w_piece26_identity leaf01260_w_suffix27_eval leaf01260_w_suffix26_join x
#print axioms leaf01260_w_suffix26_join
#print axioms leaf01260_w_suffix26_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix25 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source26.length) leaf01260_w_piece25) leaf01260_w_suffix26)
theorem leaf01260_w_suffix25_join : leaf01260_w_suffix25=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source26.length) leaf01260_w_piece25) leaf01260_w_suffix26 := by decide +kernel
theorem leaf01260_w_suffix25_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix25) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 75 leaf01260_w_source25)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 75 78
    leaf01260_w_segment25 leaf01260_w_source26 leaf01260_w_source25
    leaf01260_w_piece25 leaf01260_w_suffix26 leaf01260_w_suffix25
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source25)
    leaf01260_w_piece25_identity leaf01260_w_suffix26_eval leaf01260_w_suffix25_join x
#print axioms leaf01260_w_suffix25_join
#print axioms leaf01260_w_suffix25_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix24 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source25.length) leaf01260_w_piece24) leaf01260_w_suffix25)
theorem leaf01260_w_suffix24_join : leaf01260_w_suffix24=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source25.length) leaf01260_w_piece24) leaf01260_w_suffix25 := by decide +kernel
theorem leaf01260_w_suffix24_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix24) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_source24)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 72 75
    leaf01260_w_segment24 leaf01260_w_source25 leaf01260_w_source24
    leaf01260_w_piece24 leaf01260_w_suffix25 leaf01260_w_suffix24
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source24)
    leaf01260_w_piece24_identity leaf01260_w_suffix25_eval leaf01260_w_suffix24_join x
#print axioms leaf01260_w_suffix24_join
#print axioms leaf01260_w_suffix24_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix23 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source24.length) leaf01260_w_piece23) leaf01260_w_suffix24)
theorem leaf01260_w_suffix23_join : leaf01260_w_suffix23=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source24.length) leaf01260_w_piece23) leaf01260_w_suffix24 := by decide +kernel
theorem leaf01260_w_suffix23_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix23) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 69 leaf01260_w_source23)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 69 72
    leaf01260_w_segment23 leaf01260_w_source24 leaf01260_w_source23
    leaf01260_w_piece23 leaf01260_w_suffix24 leaf01260_w_suffix23
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source23)
    leaf01260_w_piece23_identity leaf01260_w_suffix24_eval leaf01260_w_suffix23_join x
#print axioms leaf01260_w_suffix23_join
#print axioms leaf01260_w_suffix23_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix22 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source23.length) leaf01260_w_piece22) leaf01260_w_suffix23)
theorem leaf01260_w_suffix22_join : leaf01260_w_suffix22=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source23.length) leaf01260_w_piece22) leaf01260_w_suffix23 := by decide +kernel
theorem leaf01260_w_suffix22_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix22) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 leaf01260_w_source22)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 66 69
    leaf01260_w_segment22 leaf01260_w_source23 leaf01260_w_source22
    leaf01260_w_piece22 leaf01260_w_suffix23 leaf01260_w_suffix22
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source22)
    leaf01260_w_piece22_identity leaf01260_w_suffix23_eval leaf01260_w_suffix22_join x
#print axioms leaf01260_w_suffix22_join
#print axioms leaf01260_w_suffix22_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix21 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22)
theorem leaf01260_w_suffix21_join : leaf01260_w_suffix21=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source22.length) leaf01260_w_piece21) leaf01260_w_suffix22 := by decide +kernel
theorem leaf01260_w_suffix21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix21) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_source21)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 63 66
    leaf01260_w_segment21 leaf01260_w_source22 leaf01260_w_source21
    leaf01260_w_piece21 leaf01260_w_suffix22 leaf01260_w_suffix21
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source21)
    leaf01260_w_piece21_identity leaf01260_w_suffix22_eval leaf01260_w_suffix21_join x
#print axioms leaf01260_w_suffix21_join
#print axioms leaf01260_w_suffix21_eval
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_suffix20 : NestedInteger.Poly 3 := rg_closed_integer_data%
  (NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source21.length) leaf01260_w_piece20) leaf01260_w_suffix21)
theorem leaf01260_w_suffix20_join : leaf01260_w_suffix20=NestedInteger.add (NestedInteger.scale (16^leaf01260_w_source21.length) leaf01260_w_piece20) leaf01260_w_suffix21 := by decide +kernel
theorem leaf01260_w_suffix20_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 leaf01260_w_suffix20) x=eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 60 leaf01260_w_source20)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 60 63
    leaf01260_w_segment20 leaf01260_w_source21 leaf01260_w_source20
    leaf01260_w_piece20 leaf01260_w_suffix21 leaf01260_w_suffix20
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source20)
    leaf01260_w_piece20_identity leaf01260_w_suffix21_eval leaf01260_w_suffix20_join x
#print axioms leaf01260_w_suffix20_join
#print axioms leaf01260_w_suffix20_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
