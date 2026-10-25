/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece00
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece01
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece02
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece03
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece04
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece05
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece06
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece07
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece08
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece09
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece10
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece11
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece12
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece13
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece14
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece15
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece16
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece17
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece18
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece19
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece20
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece21
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece22
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece23
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece24
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece25
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece26
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece27
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece28
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairPiece29
namespace Gebendorfer.RadenkovicGutman.D1BalancedControl1260
open NestedInteger NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def input00 : NestedInteger.Poly 3 := DegreeOneLongClass00.leaf01260_w_source00
noncomputable def input01 : NestedInteger.Poly 3 := List.take 45 input00
noncomputable def input02 : NestedInteger.Poly 3 := List.take 21 input01
noncomputable def input03 : NestedInteger.Poly 3 := List.take 9 input02
noncomputable def input04 : NestedInteger.Poly 3 := List.take 3 input03
noncomputable def input05 : NestedInteger.Poly 3 := List.drop 3 input03
noncomputable def input06 : NestedInteger.Poly 3 := List.take 3 input05
noncomputable def input07 : NestedInteger.Poly 3 := List.drop 3 input05
noncomputable def input08 : NestedInteger.Poly 3 := List.drop 9 input02
noncomputable def input09 : NestedInteger.Poly 3 := List.take 6 input08
noncomputable def input10 : NestedInteger.Poly 3 := List.take 3 input09
noncomputable def input11 : NestedInteger.Poly 3 := List.drop 3 input09
noncomputable def input12 : NestedInteger.Poly 3 := List.drop 6 input08
noncomputable def input13 : NestedInteger.Poly 3 := List.take 3 input12
noncomputable def input14 : NestedInteger.Poly 3 := List.drop 3 input12
noncomputable def input15 : NestedInteger.Poly 3 := List.drop 21 input01
noncomputable def input16 : NestedInteger.Poly 3 := List.take 12 input15
noncomputable def input17 : NestedInteger.Poly 3 := List.take 6 input16
noncomputable def input18 : NestedInteger.Poly 3 := List.take 3 input17
noncomputable def input19 : NestedInteger.Poly 3 := List.drop 3 input17
noncomputable def input20 : NestedInteger.Poly 3 := List.drop 6 input16
noncomputable def input21 : NestedInteger.Poly 3 := List.take 3 input20
noncomputable def input22 : NestedInteger.Poly 3 := List.drop 3 input20
noncomputable def input23 : NestedInteger.Poly 3 := List.drop 12 input15
noncomputable def input24 : NestedInteger.Poly 3 := List.take 6 input23
noncomputable def input25 : NestedInteger.Poly 3 := List.take 3 input24
noncomputable def input26 : NestedInteger.Poly 3 := List.drop 3 input24
noncomputable def input27 : NestedInteger.Poly 3 := List.drop 6 input23
noncomputable def input28 : NestedInteger.Poly 3 := List.take 3 input27
noncomputable def input29 : NestedInteger.Poly 3 := List.drop 3 input27
noncomputable def input30 : NestedInteger.Poly 3 := List.drop 45 input00
noncomputable def input31 : NestedInteger.Poly 3 := List.take 21 input30
noncomputable def input32 : NestedInteger.Poly 3 := List.take 9 input31
noncomputable def input33 : NestedInteger.Poly 3 := List.take 3 input32
noncomputable def input34 : NestedInteger.Poly 3 := List.drop 3 input32
noncomputable def input35 : NestedInteger.Poly 3 := List.take 3 input34
noncomputable def input36 : NestedInteger.Poly 3 := List.drop 3 input34
noncomputable def input37 : NestedInteger.Poly 3 := List.drop 9 input31
noncomputable def input38 : NestedInteger.Poly 3 := List.take 6 input37
noncomputable def input39 : NestedInteger.Poly 3 := List.take 3 input38
noncomputable def input40 : NestedInteger.Poly 3 := List.drop 3 input38
noncomputable def input41 : NestedInteger.Poly 3 := List.drop 6 input37
noncomputable def input42 : NestedInteger.Poly 3 := List.take 3 input41
noncomputable def input43 : NestedInteger.Poly 3 := List.drop 3 input41
noncomputable def input44 : NestedInteger.Poly 3 := List.drop 21 input30
noncomputable def input45 : NestedInteger.Poly 3 := List.take 12 input44
noncomputable def input46 : NestedInteger.Poly 3 := List.take 6 input45
noncomputable def input47 : NestedInteger.Poly 3 := List.take 3 input46
noncomputable def input48 : NestedInteger.Poly 3 := List.drop 3 input46
noncomputable def input49 : NestedInteger.Poly 3 := List.drop 6 input45
noncomputable def input50 : NestedInteger.Poly 3 := List.take 3 input49
noncomputable def input51 : NestedInteger.Poly 3 := List.drop 3 input49
noncomputable def input52 : NestedInteger.Poly 3 := List.drop 12 input44
noncomputable def input53 : NestedInteger.Poly 3 := List.take 6 input52
noncomputable def input54 : NestedInteger.Poly 3 := List.take 3 input53
noncomputable def input55 : NestedInteger.Poly 3 := List.drop 3 input53
noncomputable def input56 : NestedInteger.Poly 3 := List.drop 6 input52
noncomputable def input57 : NestedInteger.Poly 3 := List.take 3 input56
noncomputable def input58 : NestedInteger.Poly 3 := List.drop 3 input56
theorem split00 : input01++input30=input00 := List.take_append_drop 45 input00
#print axioms split00
theorem split01 : input02++input15=input01 := List.take_append_drop 21 input01
#print axioms split01
theorem split02 : input03++input08=input02 := List.take_append_drop 9 input02
#print axioms split02
theorem split03 : input04++input05=input03 := List.take_append_drop 3 input03
#print axioms split03
theorem input04_original : input04=DegreeOneLongClass00.leaf01260_w_segment00 := by decide +kernel
theorem leaf04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece00) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 0 input04)) x := by
  rw [input04_original,DegreeOneLongClass00.leaf01260_w_piece00_identity]
#print axioms input04_original
#print axioms leaf04_eval
theorem split05 : input06++input07=input05 := List.take_append_drop 3 input05
#print axioms split05
theorem input06_original : input06=DegreeOneLongClass00.leaf01260_w_segment01 := by decide +kernel
theorem leaf06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece01) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 3 input06)) x := by
  rw [input06_original,DegreeOneLongClass00.leaf01260_w_piece01_identity]
#print axioms input06_original
#print axioms leaf06_eval
theorem input07_original : input07=DegreeOneLongClass00.leaf01260_w_segment02 := by decide +kernel
theorem leaf07_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece02) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 6 input07)) x := by
  rw [input07_original,DegreeOneLongClass00.leaf01260_w_piece02_identity]
#print axioms input07_original
#print axioms leaf07_eval
theorem split08 : input09++input12=input08 := List.take_append_drop 6 input08
#print axioms split08
theorem split09 : input10++input11=input09 := List.take_append_drop 3 input09
#print axioms split09
theorem input10_original : input10=DegreeOneLongClass00.leaf01260_w_segment03 := by decide +kernel
theorem leaf10_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece03) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 9 input10)) x := by
  rw [input10_original,DegreeOneLongClass00.leaf01260_w_piece03_identity]
#print axioms input10_original
#print axioms leaf10_eval
theorem input11_original : input11=DegreeOneLongClass00.leaf01260_w_segment04 := by decide +kernel
theorem leaf11_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece04) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 12 input11)) x := by
  rw [input11_original,DegreeOneLongClass00.leaf01260_w_piece04_identity]
#print axioms input11_original
#print axioms leaf11_eval
theorem split12 : input13++input14=input12 := List.take_append_drop 3 input12
#print axioms split12
theorem input13_original : input13=DegreeOneLongClass00.leaf01260_w_segment05 := by decide +kernel
theorem leaf13_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece05) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 15 input13)) x := by
  rw [input13_original,DegreeOneLongClass00.leaf01260_w_piece05_identity]
#print axioms input13_original
#print axioms leaf13_eval
theorem input14_original : input14=DegreeOneLongClass00.leaf01260_w_segment06 := by decide +kernel
theorem leaf14_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece06) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 18 input14)) x := by
  rw [input14_original,DegreeOneLongClass00.leaf01260_w_piece06_identity]
#print axioms input14_original
#print axioms leaf14_eval
theorem split15 : input16++input23=input15 := List.take_append_drop 12 input15
#print axioms split15
theorem split16 : input17++input20=input16 := List.take_append_drop 6 input16
#print axioms split16
theorem split17 : input18++input19=input17 := List.take_append_drop 3 input17
#print axioms split17
theorem input18_original : input18=DegreeOneLongClass00.leaf01260_w_segment07 := by decide +kernel
theorem leaf18_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece07) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 21 input18)) x := by
  rw [input18_original,DegreeOneLongClass00.leaf01260_w_piece07_identity]
#print axioms input18_original
#print axioms leaf18_eval
theorem input19_original : input19=DegreeOneLongClass00.leaf01260_w_segment08 := by decide +kernel
theorem leaf19_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece08) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 24 input19)) x := by
  rw [input19_original,DegreeOneLongClass00.leaf01260_w_piece08_identity]
#print axioms input19_original
#print axioms leaf19_eval
theorem split20 : input21++input22=input20 := List.take_append_drop 3 input20
#print axioms split20
theorem input21_original : input21=DegreeOneLongClass00.leaf01260_w_segment09 := by decide +kernel
theorem leaf21_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece09) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 27 input21)) x := by
  rw [input21_original,DegreeOneLongClass00.leaf01260_w_piece09_identity]
#print axioms input21_original
#print axioms leaf21_eval
theorem input22_original : input22=DegreeOneLongClass00.leaf01260_w_segment10 := by decide +kernel
theorem leaf22_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece10) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 30 input22)) x := by
  rw [input22_original,DegreeOneLongClass00.leaf01260_w_piece10_identity]
#print axioms input22_original
#print axioms leaf22_eval
theorem split23 : input24++input27=input23 := List.take_append_drop 6 input23
#print axioms split23
theorem split24 : input25++input26=input24 := List.take_append_drop 3 input24
#print axioms split24
theorem input25_original : input25=DegreeOneLongClass00.leaf01260_w_segment11 := by decide +kernel
theorem leaf25_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece11) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 33 input25)) x := by
  rw [input25_original,DegreeOneLongClass00.leaf01260_w_piece11_identity]
#print axioms input25_original
#print axioms leaf25_eval
theorem input26_original : input26=DegreeOneLongClass00.leaf01260_w_segment12 := by decide +kernel
theorem leaf26_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece12) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 36 input26)) x := by
  rw [input26_original,DegreeOneLongClass00.leaf01260_w_piece12_identity]
#print axioms input26_original
#print axioms leaf26_eval
theorem split27 : input28++input29=input27 := List.take_append_drop 3 input27
#print axioms split27
theorem input28_original : input28=DegreeOneLongClass00.leaf01260_w_segment13 := by decide +kernel
theorem leaf28_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece13) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 39 input28)) x := by
  rw [input28_original,DegreeOneLongClass00.leaf01260_w_piece13_identity]
#print axioms input28_original
#print axioms leaf28_eval
theorem input29_original : input29=DegreeOneLongClass00.leaf01260_w_segment14 := by decide +kernel
theorem leaf29_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece14) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 42 input29)) x := by
  rw [input29_original,DegreeOneLongClass00.leaf01260_w_piece14_identity]
#print axioms input29_original
#print axioms leaf29_eval
theorem split30 : input31++input44=input30 := List.take_append_drop 21 input30
#print axioms split30
theorem split31 : input32++input37=input31 := List.take_append_drop 9 input31
#print axioms split31
theorem split32 : input33++input34=input32 := List.take_append_drop 3 input32
#print axioms split32
theorem input33_original : input33=DegreeOneLongClass00.leaf01260_w_segment15 := by decide +kernel
theorem leaf33_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece15) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 45 input33)) x := by
  rw [input33_original,DegreeOneLongClass00.leaf01260_w_piece15_identity]
#print axioms input33_original
#print axioms leaf33_eval
theorem split34 : input35++input36=input34 := List.take_append_drop 3 input34
#print axioms split34
theorem input35_original : input35=DegreeOneLongClass00.leaf01260_w_segment16 := by decide +kernel
theorem leaf35_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece16) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 48 input35)) x := by
  rw [input35_original,DegreeOneLongClass00.leaf01260_w_piece16_identity]
#print axioms input35_original
#print axioms leaf35_eval
theorem input36_original : input36=DegreeOneLongClass00.leaf01260_w_segment17 := by decide +kernel
theorem leaf36_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece17) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 51 input36)) x := by
  rw [input36_original,DegreeOneLongClass00.leaf01260_w_piece17_identity]
#print axioms input36_original
#print axioms leaf36_eval
theorem split37 : input38++input41=input37 := List.take_append_drop 6 input37
#print axioms split37
theorem split38 : input39++input40=input38 := List.take_append_drop 3 input38
#print axioms split38
theorem input39_original : input39=DegreeOneLongClass00.leaf01260_w_segment18 := by decide +kernel
theorem leaf39_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece18) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 54 input39)) x := by
  rw [input39_original,DegreeOneLongClass00.leaf01260_w_piece18_identity]
#print axioms input39_original
#print axioms leaf39_eval
theorem input40_original : input40=DegreeOneLongClass00.leaf01260_w_segment19 := by decide +kernel
theorem leaf40_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece19) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 57 input40)) x := by
  rw [input40_original,DegreeOneLongClass00.leaf01260_w_piece19_identity]
#print axioms input40_original
#print axioms leaf40_eval
theorem split41 : input42++input43=input41 := List.take_append_drop 3 input41
#print axioms split41
theorem input42_original : input42=DegreeOneLongClass00.leaf01260_w_segment20 := by decide +kernel
theorem leaf42_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece20) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 60 input42)) x := by
  rw [input42_original,DegreeOneLongClass00.leaf01260_w_piece20_identity]
#print axioms input42_original
#print axioms leaf42_eval
theorem input43_original : input43=DegreeOneLongClass00.leaf01260_w_segment21 := by decide +kernel
theorem leaf43_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece21) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 63 input43)) x := by
  rw [input43_original,DegreeOneLongClass00.leaf01260_w_piece21_identity]
#print axioms input43_original
#print axioms leaf43_eval
theorem split44 : input45++input52=input44 := List.take_append_drop 12 input44
#print axioms split44
theorem split45 : input46++input49=input45 := List.take_append_drop 6 input45
#print axioms split45
theorem split46 : input47++input48=input46 := List.take_append_drop 3 input46
#print axioms split46
theorem input47_original : input47=DegreeOneLongClass00.leaf01260_w_segment22 := by decide +kernel
theorem leaf47_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece22) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 66 input47)) x := by
  rw [input47_original,DegreeOneLongClass00.leaf01260_w_piece22_identity]
#print axioms input47_original
#print axioms leaf47_eval
theorem input48_original : input48=DegreeOneLongClass00.leaf01260_w_segment23 := by decide +kernel
theorem leaf48_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece23) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 69 input48)) x := by
  rw [input48_original,DegreeOneLongClass00.leaf01260_w_piece23_identity]
#print axioms input48_original
#print axioms leaf48_eval
theorem split49 : input50++input51=input49 := List.take_append_drop 3 input49
#print axioms split49
theorem input50_original : input50=DegreeOneLongClass00.leaf01260_w_segment24 := by decide +kernel
theorem leaf50_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece24) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 72 input50)) x := by
  rw [input50_original,DegreeOneLongClass00.leaf01260_w_piece24_identity]
#print axioms input50_original
#print axioms leaf50_eval
theorem input51_original : input51=DegreeOneLongClass00.leaf01260_w_segment25 := by decide +kernel
theorem leaf51_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece25) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 75 input51)) x := by
  rw [input51_original,DegreeOneLongClass00.leaf01260_w_piece25_identity]
#print axioms input51_original
#print axioms leaf51_eval
theorem split52 : input53++input56=input52 := List.take_append_drop 6 input52
#print axioms split52
theorem split53 : input54++input55=input53 := List.take_append_drop 3 input53
#print axioms split53
theorem input54_original : input54=DegreeOneLongClass00.leaf01260_w_segment26 := by decide +kernel
theorem leaf54_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece26) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 78 input54)) x := by
  rw [input54_original,DegreeOneLongClass00.leaf01260_w_piece26_identity]
#print axioms input54_original
#print axioms leaf54_eval
theorem input55_original : input55=DegreeOneLongClass00.leaf01260_w_segment27 := by decide +kernel
theorem leaf55_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece27) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 81 input55)) x := by
  rw [input55_original,DegreeOneLongClass00.leaf01260_w_piece27_identity]
#print axioms input55_original
#print axioms leaf55_eval
theorem split56 : input57++input58=input56 := List.take_append_drop 3 input56
#print axioms split56
theorem input57_original : input57=DegreeOneLongClass00.leaf01260_w_segment28 := by decide +kernel
theorem leaf57_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece28) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 84 input57)) x := by
  rw [input57_original,DegreeOneLongClass00.leaf01260_w_piece28_identity]
#print axioms input57_original
#print axioms leaf57_eval
theorem input58_original : input58=DegreeOneLongClass00.leaf01260_w_segment29 := by decide +kernel
theorem leaf58_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 DegreeOneLongClass00.leaf01260_w_piece29) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 8 1 16 87 input58)) x := by
  rw [input58_original,DegreeOneLongClass00.leaf01260_w_piece29_identity]
#print axioms input58_original
#print axioms leaf58_eval
end Gebendorfer.RadenkovicGutman.D1BalancedControl1260
