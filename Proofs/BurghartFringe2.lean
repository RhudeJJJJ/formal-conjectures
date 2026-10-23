import Proofs.BurghartRoot2Part0
import Proofs.BurghartRoot2Part1
import Proofs.BurghartRoot2Part2
import Proofs.BurghartRoot2Part3
import Proofs.BurghartRoot2Part4
import Proofs.BurghartRoot2Part5
import Proofs.BurghartRoot2Part6
import Proofs.BurghartRoot2Part7
import Proofs.BurghartRoot2Part8
import Proofs.BurghartRoot2Part9
import Proofs.BurghartRoot2Part10
import Proofs.BurghartRoot2Part11
import Proofs.BurghartRoot2Part12
import Proofs.BurghartRoot2Part13
import Proofs.BurghartRoot2Part14
import Proofs.BurghartRoot2Part15
/-! # Complete fringe polynomial certificates for witness 2 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
theorem rootParts2_correct (i : Fin 16) : norm1 (fringePart T2 distances2 0 i) = rootParts2 i := by
  fin_cases i
  · exact root2_part0
  · exact root2_part1
  · exact root2_part2
  · exact root2_part3
  · exact root2_part4
  · exact root2_part5
  · exact root2_part6
  · exact root2_part7
  · exact root2_part8
  · exact root2_part9
  · exact root2_part10
  · exact root2_part11
  · exact root2_part12
  · exact root2_part13
  · exact root2_part14
  · exact root2_part15
theorem fringe2_0 : eval1 (fringeVec T2 distances2 0) = eval1 (fringeTable2 0) :=
  eval_fringe_from_parts T2 distances2 0 rootParts2 (fringeTable2 0) rootParts2_correct rootParts2_sum
set_option maxHeartbeats 0 in
theorem fringe2_1 : norm1 (fringeVec T2 distances2 1) = fringeTable2 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_2 : norm1 (fringeVec T2 distances2 2) = fringeTable2 2 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_3 : norm1 (fringeVec T2 distances2 3) = fringeTable2 3 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_4 : norm1 (fringeVec T2 distances2 4) = fringeTable2 4 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_5 : norm1 (fringeVec T2 distances2 5) = fringeTable2 5 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_6 : norm1 (fringeVec T2 distances2 6) = fringeTable2 6 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_7 : norm1 (fringeVec T2 distances2 7) = fringeTable2 7 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_8 : norm1 (fringeVec T2 distances2 8) = fringeTable2 8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_9 : norm1 (fringeVec T2 distances2 9) = fringeTable2 9 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_10 : norm1 (fringeVec T2 distances2 10) = fringeTable2 10 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_11 : norm1 (fringeVec T2 distances2 11) = fringeTable2 11 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_12 : norm1 (fringeVec T2 distances2 12) = fringeTable2 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_13 : norm1 (fringeVec T2 distances2 13) = fringeTable2 13 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_14 : norm1 (fringeVec T2 distances2 14) = fringeTable2 14 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_15 : norm1 (fringeVec T2 distances2 15) = fringeTable2 15 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_16 : norm1 (fringeVec T2 distances2 16) = fringeTable2 16 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_17 : norm1 (fringeVec T2 distances2 17) = fringeTable2 17 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_18 : norm1 (fringeVec T2 distances2 18) = fringeTable2 18 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_19 : norm1 (fringeVec T2 distances2 19) = fringeTable2 19 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_20 : norm1 (fringeVec T2 distances2 20) = fringeTable2 20 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_21 : norm1 (fringeVec T2 distances2 21) = fringeTable2 21 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_22 : norm1 (fringeVec T2 distances2 22) = fringeTable2 22 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_23 : norm1 (fringeVec T2 distances2 23) = fringeTable2 23 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_24 : norm1 (fringeVec T2 distances2 24) = fringeTable2 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_25 : norm1 (fringeVec T2 distances2 25) = fringeTable2 25 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_26 : norm1 (fringeVec T2 distances2 26) = fringeTable2 26 := by decide +kernel
set_option maxHeartbeats 0 in
theorem fringe2_27 : norm1 (fringeVec T2 distances2 27) = fringeTable2 27 := by decide +kernel
theorem fringeTable2_correct (v : Fin 28) : eval1 (fringeVec T2 distances2 v) = eval1 (fringeTable2 v) := by
  fin_cases v
  · exact fringe2_0
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_1)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_2)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_3)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_4)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_5)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_6)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_7)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_8)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_9)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_10)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_11)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_12)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_13)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_14)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_15)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_16)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_17)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_18)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_19)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_20)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_21)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_22)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_23)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_24)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_25)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_26)
  · exact (eval_norm1 _).symm.trans (congrArg eval1 fringe2_27)
#print axioms fringeTable2_correct
end BurghartLists
