import Proofs.BurghartRoot1Part0
import Proofs.BurghartRoot1Part1
import Proofs.BurghartRoot1Part2
import Proofs.BurghartRoot1Part3
import Proofs.BurghartRoot1Part4
import Proofs.BurghartRoot1Part5
import Proofs.BurghartRoot1Part6
import Proofs.BurghartRoot1Part7
import Proofs.BurghartRoot1Part8
import Proofs.BurghartRoot1Part9
import Proofs.BurghartRoot1Part10
import Proofs.BurghartRoot1Part11
import Proofs.BurghartRoot1Part12
import Proofs.BurghartRoot1Part13
import Proofs.BurghartRoot1Part14
import Proofs.BurghartRoot1Part15
/-! # Complete fringe polynomial certificates for witness 1 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
theorem rootParts1_correct (i : Fin 16) : norm1 (fringePart T1 distances1 0 i) = rootParts1 i := by
  fin_cases i
  · exact root1_part0
  · exact root1_part1
  · exact root1_part2
  · exact root1_part3
  · exact root1_part4
  · exact root1_part5
  · exact root1_part6
  · exact root1_part7
  · exact root1_part8
  · exact root1_part9
  · exact root1_part10
  · exact root1_part11
  · exact root1_part12
  · exact root1_part13
  · exact root1_part14
  · exact root1_part15
theorem fringe1_0 : eval1 (fringeVec T1 distances1 0) = eval1 (fringeTable1 0) :=
  eval_fringe_from_parts T1 distances1 0 rootParts1 (fringeTable1 0) rootParts1_correct rootParts1_sum
set_option maxHeartbeats 0 in
theorem fringe1_1 : norm1 (fringeVec T1 distances1 1) = fringeTable1 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_2 : norm1 (fringeVec T1 distances1 2) = fringeTable1 2 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_3 : norm1 (fringeVec T1 distances1 3) = fringeTable1 3 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_4 : norm1 (fringeVec T1 distances1 4) = fringeTable1 4 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_5 : norm1 (fringeVec T1 distances1 5) = fringeTable1 5 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_6 : norm1 (fringeVec T1 distances1 6) = fringeTable1 6 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_7 : norm1 (fringeVec T1 distances1 7) = fringeTable1 7 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_8 : norm1 (fringeVec T1 distances1 8) = fringeTable1 8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_9 : norm1 (fringeVec T1 distances1 9) = fringeTable1 9 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_10 : norm1 (fringeVec T1 distances1 10) = fringeTable1 10 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_11 : norm1 (fringeVec T1 distances1 11) = fringeTable1 11 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_12 : norm1 (fringeVec T1 distances1 12) = fringeTable1 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_13 : norm1 (fringeVec T1 distances1 13) = fringeTable1 13 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_14 : norm1 (fringeVec T1 distances1 14) = fringeTable1 14 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_15 : norm1 (fringeVec T1 distances1 15) = fringeTable1 15 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_16 : norm1 (fringeVec T1 distances1 16) = fringeTable1 16 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_17 : norm1 (fringeVec T1 distances1 17) = fringeTable1 17 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_18 : norm1 (fringeVec T1 distances1 18) = fringeTable1 18 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_19 : norm1 (fringeVec T1 distances1 19) = fringeTable1 19 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_20 : norm1 (fringeVec T1 distances1 20) = fringeTable1 20 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_21 : norm1 (fringeVec T1 distances1 21) = fringeTable1 21 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_22 : norm1 (fringeVec T1 distances1 22) = fringeTable1 22 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_23 : norm1 (fringeVec T1 distances1 23) = fringeTable1 23 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_24 : norm1 (fringeVec T1 distances1 24) = fringeTable1 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_25 : norm1 (fringeVec T1 distances1 25) = fringeTable1 25 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_26 : norm1 (fringeVec T1 distances1 26) = fringeTable1 26 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe1_27 : norm1 (fringeVec T1 distances1 27) = fringeTable1 27 := by decide +kernel
theorem fringeTable1_correct (v : Fin 28) : eval1 (fringeVec T1 distances1 v) = eval1 (fringeTable1 v) := by
  fin_cases v
  · exact fringe1_0
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_1)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_2)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_3)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_4)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_5)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_6)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_7)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_8)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_9)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_10)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_11)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_12)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_13)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_14)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_15)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_16)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_17)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_18)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_19)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_20)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_21)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_22)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_23)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_24)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_25)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_26)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe1_27)
#print axioms fringeTable1_correct
end BurghartLists
