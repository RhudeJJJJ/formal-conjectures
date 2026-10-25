/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260NoRuntimeSegmented
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf01260_rejoined_suffix29_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix29) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 87 leaf01260_w_source29)) x :=
  leaf01260_w_suffix29_eval x
#print axioms leaf01260_rejoined_suffix29_eval
theorem leaf01260_rejoined_suffix28_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix28) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_source28)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 84 87
    leaf01260_w_segment28 leaf01260_w_source29 leaf01260_w_source28
    leaf01260_w_piece28 leaf01260_w_suffix29 leaf01260_w_suffix28
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source28)
    leaf01260_w_piece28_identity leaf01260_rejoined_suffix29_eval leaf01260_w_suffix28_join x
#print axioms leaf01260_rejoined_suffix28_eval
theorem leaf01260_rejoined_suffix27_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix27) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 81 84
    leaf01260_w_segment27 leaf01260_w_source28 leaf01260_w_source27
    leaf01260_w_piece27 leaf01260_w_suffix28 leaf01260_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source27)
    leaf01260_w_piece27_identity leaf01260_rejoined_suffix28_eval leaf01260_w_suffix27_join x
#print axioms leaf01260_rejoined_suffix27_eval
theorem leaf01260_rejoined_suffix26_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix26) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 leaf01260_w_source26)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 78 81
    leaf01260_w_segment26 leaf01260_w_source27 leaf01260_w_source26
    leaf01260_w_piece26 leaf01260_w_suffix27 leaf01260_w_suffix26
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source26)
    leaf01260_w_piece26_identity leaf01260_rejoined_suffix27_eval leaf01260_w_suffix26_join x
#print axioms leaf01260_rejoined_suffix26_eval
theorem leaf01260_rejoined_suffix25_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix25) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 75 leaf01260_w_source25)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 75 78
    leaf01260_w_segment25 leaf01260_w_source26 leaf01260_w_source25
    leaf01260_w_piece25 leaf01260_w_suffix26 leaf01260_w_suffix25
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source25)
    leaf01260_w_piece25_identity leaf01260_rejoined_suffix26_eval leaf01260_w_suffix25_join x
#print axioms leaf01260_rejoined_suffix25_eval
theorem leaf01260_rejoined_suffix24_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix24) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 leaf01260_w_source24)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 72 75
    leaf01260_w_segment24 leaf01260_w_source25 leaf01260_w_source24
    leaf01260_w_piece24 leaf01260_w_suffix25 leaf01260_w_suffix24
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source24)
    leaf01260_w_piece24_identity leaf01260_rejoined_suffix25_eval leaf01260_w_suffix24_join x
#print axioms leaf01260_rejoined_suffix24_eval
theorem leaf01260_rejoined_suffix23_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix23) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 69 leaf01260_w_source23)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 69 72
    leaf01260_w_segment23 leaf01260_w_source24 leaf01260_w_source23
    leaf01260_w_piece23 leaf01260_w_suffix24 leaf01260_w_suffix23
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source23)
    leaf01260_w_piece23_identity leaf01260_rejoined_suffix24_eval leaf01260_w_suffix23_join x
#print axioms leaf01260_rejoined_suffix23_eval
theorem leaf01260_rejoined_suffix22_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix22) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 leaf01260_w_source22)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 66 69
    leaf01260_w_segment22 leaf01260_w_source23 leaf01260_w_source22
    leaf01260_w_piece22 leaf01260_w_suffix23 leaf01260_w_suffix22
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source22)
    leaf01260_w_piece22_identity leaf01260_rejoined_suffix23_eval leaf01260_w_suffix22_join x
#print axioms leaf01260_rejoined_suffix22_eval
theorem leaf01260_rejoined_suffix21_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix21) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 leaf01260_w_source21)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 63 66
    leaf01260_w_segment21 leaf01260_w_source22 leaf01260_w_source21
    leaf01260_w_piece21 leaf01260_w_suffix22 leaf01260_w_suffix21
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source21)
    leaf01260_w_piece21_identity leaf01260_rejoined_suffix22_eval leaf01260_w_suffix21_join x
#print axioms leaf01260_rejoined_suffix21_eval
theorem leaf01260_rejoined_suffix20_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix20) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 60 leaf01260_w_source20)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 60 63
    leaf01260_w_segment20 leaf01260_w_source21 leaf01260_w_source20
    leaf01260_w_piece20 leaf01260_w_suffix21 leaf01260_w_suffix20
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source20)
    leaf01260_w_piece20_identity leaf01260_rejoined_suffix21_eval leaf01260_w_suffix20_join x
#print axioms leaf01260_rejoined_suffix20_eval
theorem leaf01260_rejoined_suffix19_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix19) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 57 leaf01260_w_source19)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 57 60
    leaf01260_w_segment19 leaf01260_w_source20 leaf01260_w_source19
    leaf01260_w_piece19 leaf01260_w_suffix20 leaf01260_w_suffix19
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source19)
    leaf01260_w_piece19_identity leaf01260_rejoined_suffix20_eval leaf01260_w_suffix19_join x
#print axioms leaf01260_rejoined_suffix19_eval
theorem leaf01260_rejoined_suffix18_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix18) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 leaf01260_w_source18)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 54 57
    leaf01260_w_segment18 leaf01260_w_source19 leaf01260_w_source18
    leaf01260_w_piece18 leaf01260_w_suffix19 leaf01260_w_suffix18
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source18)
    leaf01260_w_piece18_identity leaf01260_rejoined_suffix19_eval leaf01260_w_suffix18_join x
#print axioms leaf01260_rejoined_suffix18_eval
theorem leaf01260_rejoined_suffix17_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix17) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 leaf01260_w_source17)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 51 54
    leaf01260_w_segment17 leaf01260_w_source18 leaf01260_w_source17
    leaf01260_w_piece17 leaf01260_w_suffix18 leaf01260_w_suffix17
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source17)
    leaf01260_w_piece17_identity leaf01260_rejoined_suffix18_eval leaf01260_w_suffix17_join x
#print axioms leaf01260_rejoined_suffix17_eval
theorem leaf01260_rejoined_suffix16_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix16) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 leaf01260_w_source16)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 48 51
    leaf01260_w_segment16 leaf01260_w_source17 leaf01260_w_source16
    leaf01260_w_piece16 leaf01260_w_suffix17 leaf01260_w_suffix16
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source16)
    leaf01260_w_piece16_identity leaf01260_rejoined_suffix17_eval leaf01260_w_suffix16_join x
#print axioms leaf01260_rejoined_suffix16_eval
theorem leaf01260_rejoined_suffix15_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix15) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 leaf01260_w_source15)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 45 48
    leaf01260_w_segment15 leaf01260_w_source16 leaf01260_w_source15
    leaf01260_w_piece15 leaf01260_w_suffix16 leaf01260_w_suffix15
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source15)
    leaf01260_w_piece15_identity leaf01260_rejoined_suffix16_eval leaf01260_w_suffix15_join x
#print axioms leaf01260_rejoined_suffix15_eval
theorem leaf01260_rejoined_suffix14_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix14) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 leaf01260_w_source14)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 42 45
    leaf01260_w_segment14 leaf01260_w_source15 leaf01260_w_source14
    leaf01260_w_piece14 leaf01260_w_suffix15 leaf01260_w_suffix14
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source14)
    leaf01260_w_piece14_identity leaf01260_rejoined_suffix15_eval leaf01260_w_suffix14_join x
#print axioms leaf01260_rejoined_suffix14_eval
theorem leaf01260_rejoined_suffix13_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix13) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 39 leaf01260_w_source13)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 39 42
    leaf01260_w_segment13 leaf01260_w_source14 leaf01260_w_source13
    leaf01260_w_piece13 leaf01260_w_suffix14 leaf01260_w_suffix13
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source13)
    leaf01260_w_piece13_identity leaf01260_rejoined_suffix14_eval leaf01260_w_suffix13_join x
#print axioms leaf01260_rejoined_suffix13_eval
theorem leaf01260_rejoined_suffix12_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix12) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 36 leaf01260_w_source12)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 36 39
    leaf01260_w_segment12 leaf01260_w_source13 leaf01260_w_source12
    leaf01260_w_piece12 leaf01260_w_suffix13 leaf01260_w_suffix12
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source12)
    leaf01260_w_piece12_identity leaf01260_rejoined_suffix13_eval leaf01260_w_suffix12_join x
#print axioms leaf01260_rejoined_suffix12_eval
theorem leaf01260_rejoined_suffix11_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix11) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 leaf01260_w_source11)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 33 36
    leaf01260_w_segment11 leaf01260_w_source12 leaf01260_w_source11
    leaf01260_w_piece11 leaf01260_w_suffix12 leaf01260_w_suffix11
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source11)
    leaf01260_w_piece11_identity leaf01260_rejoined_suffix12_eval leaf01260_w_suffix11_join x
#print axioms leaf01260_rejoined_suffix11_eval
theorem leaf01260_rejoined_suffix10_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix10) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 30 leaf01260_w_source10)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 30 33
    leaf01260_w_segment10 leaf01260_w_source11 leaf01260_w_source10
    leaf01260_w_piece10 leaf01260_w_suffix11 leaf01260_w_suffix10
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source10)
    leaf01260_w_piece10_identity leaf01260_rejoined_suffix11_eval leaf01260_w_suffix10_join x
#print axioms leaf01260_rejoined_suffix10_eval
theorem leaf01260_rejoined_suffix09_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix09) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 27 leaf01260_w_source09)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 27 30
    leaf01260_w_segment09 leaf01260_w_source10 leaf01260_w_source09
    leaf01260_w_piece09 leaf01260_w_suffix10 leaf01260_w_suffix09
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source09)
    leaf01260_w_piece09_identity leaf01260_rejoined_suffix10_eval leaf01260_w_suffix09_join x
#print axioms leaf01260_rejoined_suffix09_eval
theorem leaf01260_rejoined_suffix08_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix08) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 24 leaf01260_w_source08)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 24 27
    leaf01260_w_segment08 leaf01260_w_source09 leaf01260_w_source08
    leaf01260_w_piece08 leaf01260_w_suffix09 leaf01260_w_suffix08
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source08)
    leaf01260_w_piece08_identity leaf01260_rejoined_suffix09_eval leaf01260_w_suffix08_join x
#print axioms leaf01260_rejoined_suffix08_eval
theorem leaf01260_rejoined_suffix07_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix07) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 leaf01260_w_source07)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 21 24
    leaf01260_w_segment07 leaf01260_w_source08 leaf01260_w_source07
    leaf01260_w_piece07 leaf01260_w_suffix08 leaf01260_w_suffix07
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source07)
    leaf01260_w_piece07_identity leaf01260_rejoined_suffix08_eval leaf01260_w_suffix07_join x
#print axioms leaf01260_rejoined_suffix07_eval
theorem leaf01260_rejoined_suffix06_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix06) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 18 leaf01260_w_source06)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 18 21
    leaf01260_w_segment06 leaf01260_w_source07 leaf01260_w_source06
    leaf01260_w_piece06 leaf01260_w_suffix07 leaf01260_w_suffix06
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source06)
    leaf01260_w_piece06_identity leaf01260_rejoined_suffix07_eval leaf01260_w_suffix06_join x
#print axioms leaf01260_rejoined_suffix06_eval
theorem leaf01260_rejoined_suffix05_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix05) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 15 leaf01260_w_source05)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 15 18
    leaf01260_w_segment05 leaf01260_w_source06 leaf01260_w_source05
    leaf01260_w_piece05 leaf01260_w_suffix06 leaf01260_w_suffix05
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source05)
    leaf01260_w_piece05_identity leaf01260_rejoined_suffix06_eval leaf01260_w_suffix05_join x
#print axioms leaf01260_rejoined_suffix05_eval
theorem leaf01260_rejoined_suffix04_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix04) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 12 leaf01260_w_source04)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 12 15
    leaf01260_w_segment04 leaf01260_w_source05 leaf01260_w_source04
    leaf01260_w_piece04 leaf01260_w_suffix05 leaf01260_w_suffix04
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source04)
    leaf01260_w_piece04_identity leaf01260_rejoined_suffix05_eval leaf01260_w_suffix04_join x
#print axioms leaf01260_rejoined_suffix04_eval
theorem leaf01260_rejoined_suffix03_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix03) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 leaf01260_w_source03)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 9 12
    leaf01260_w_segment03 leaf01260_w_source04 leaf01260_w_source03
    leaf01260_w_piece03 leaf01260_w_suffix04 leaf01260_w_suffix03
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source03)
    leaf01260_w_piece03_identity leaf01260_rejoined_suffix04_eval leaf01260_w_suffix03_join x
#print axioms leaf01260_rejoined_suffix03_eval
theorem leaf01260_rejoined_suffix02_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix02) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 6 leaf01260_w_source02)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 6 9
    leaf01260_w_segment02 leaf01260_w_source03 leaf01260_w_source02
    leaf01260_w_piece02 leaf01260_w_suffix03 leaf01260_w_suffix02
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source02)
    leaf01260_w_piece02_identity leaf01260_rejoined_suffix03_eval leaf01260_w_suffix02_join x
#print axioms leaf01260_rejoined_suffix02_eval
theorem leaf01260_rejoined_suffix01_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix01) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 3 leaf01260_w_source01)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 3 6
    leaf01260_w_segment01 leaf01260_w_source02 leaf01260_w_source01
    leaf01260_w_piece01 leaf01260_w_suffix02 leaf01260_w_suffix01
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source01)
    leaf01260_w_piece01_identity leaf01260_rejoined_suffix02_eval leaf01260_w_suffix01_join x
#print axioms leaf01260_rejoined_suffix01_eval
theorem leaf01260_rejoined_affine_eval (x : Fin 3 → ℝ) :
  NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_affine) x=
    NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_source00)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 0 3
    leaf01260_w_segment00 leaf01260_w_source01 leaf01260_w_source00
    leaf01260_w_piece00 leaf01260_w_suffix01 leaf01260_w_affine
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source00)
    leaf01260_w_piece00_identity leaf01260_rejoined_suffix01_eval leaf01260_w_affine_join x
#print axioms leaf01260_rejoined_affine_eval
theorem leaf01260_rejoined_checked : FastNestedCellData.accepts 1 4 4 leaf01260=true :=
  IntegerPiecewiseCell.accepts_make DegreeOneIntegerNorm00.pack true (890775397/25000000000) (5091891099/4294967296) (365513211/4294967296) 0 8 ![88,4,4] ![(1/2),(1/2),(1/2)] ![(1/16),(1/4),(1/2)]
    95646279954910412800000000000 117433600742788206146848872291 3295825219754812282575000000000 ![8,2,1] ![1,1,1] ![16,4,2] leaf01260_w_raw leaf01260_w_inner leaf01260_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01260_raw leaf01260_rectangular leaf01260_inner leaf01260_rejoined_affine_eval leaf01260_sign leaf01260_log
#print axioms leaf01260_rejoined_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
