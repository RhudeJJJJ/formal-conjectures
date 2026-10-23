import Proofs.BurghartVectors
/-! # Complete fringe polynomial certificates for witness 1 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
def fringeTable1 (v : Fin 28) : V1 := (([[0,0,1,1,7,-9,-6,-1,-7,52,-26,-23,5,-66,145,-27,-88,57,-114,184,-6,-208,165,0,-65,39,-10,1],[0,0,1,3,-3,-1,-2,1,8,-6,-3,4,-1],[0,1,3,-3,-1,-2,1,8,-6,-3,4,-1],[0,1,0,2,-3,1],[0,0,2,-1],[0,2,-1],[1],[1],[1],[0,1],[1],[0,1],[1],[1],[0,1,0,4,-5,-2,2,-2,13,-12,-5,12,-6,1],[0,0,4,-1,-3,-1,-3,10,-2,-7,5,-1],[0,0,1,1,-1],[0,1,1,-1],[0,1],[1],[1],[0,2,-1],[1],[1],[0,2,-1],[1],[1],[1]]: List V1).getD v.val [])

set_option maxHeartbeats 0 in
theorem fringe1_0 : norm1 (fringeVec T1 distances1 0) = fringeTable1 0 := by decide +kernel
#print axioms fringe1_0
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
theorem fringeTable1_correct (v : Fin 28) : norm1 (fringeVec T1 distances1 v) = fringeTable1 v := by
  fin_cases v
  · exact fringe1_0
  · exact fringe1_1
  · exact fringe1_2
  · exact fringe1_3
  · exact fringe1_4
  · exact fringe1_5
  · exact fringe1_6
  · exact fringe1_7
  · exact fringe1_8
  · exact fringe1_9
  · exact fringe1_10
  · exact fringe1_11
  · exact fringe1_12
  · exact fringe1_13
  · exact fringe1_14
  · exact fringe1_15
  · exact fringe1_16
  · exact fringe1_17
  · exact fringe1_18
  · exact fringe1_19
  · exact fringe1_20
  · exact fringe1_21
  · exact fringe1_22
  · exact fringe1_23
  · exact fringe1_24
  · exact fringe1_25
  · exact fringe1_26
  · exact fringe1_27
#print axioms fringeTable1_correct
end BurghartLists
