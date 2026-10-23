import Proofs.BurghartVectors
/-! # Complete fringe polynomial certificates for witness 2 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
def fringeTable2 (v : Fin 28) : V1 := (([[0,0,1,1,7,-9,-6,-1,-7,52,-26,-23,5,-66,145,-27,-88,57,-114,184,-6,-208,165,0,-65,39,-10,1],[0,1,0,4,-5,-2,2,-2,13,-12,-5,12,-6,1],[0,0,4,-1,-3,-1,-3,10,-2,-7,5,-1],[0,1,0,2,-3,1],[0,0,2,-1],[0,2,-1],[1],[1],[1],[0,2,-1],[1],[1],[0,1],[1],[1],[0,0,1,3,-3,-1,-2,1,8,-6,-3,4,-1],[0,1,3,-3,-1,-2,1,8,-6,-3,4,-1],[0,0,1,1,-1],[0,1,1,-1],[0,1],[1],[1],[0,2,-1],[1],[1],[0,1],[1],[1]]: List V1).getD v.val [])

set_option maxHeartbeats 0 in
theorem fringe2_0 : norm1 (fringeVec T2 distances2 0) = fringeTable2 0 := by decide +kernel
#print axioms fringe2_0
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
theorem fringeTable2_correct (v : Fin 28) : norm1 (fringeVec T2 distances2 v) = fringeTable2 v := by
  fin_cases v
  · exact fringe2_0
  · exact fringe2_1
  · exact fringe2_2
  · exact fringe2_3
  · exact fringe2_4
  · exact fringe2_5
  · exact fringe2_6
  · exact fringe2_7
  · exact fringe2_8
  · exact fringe2_9
  · exact fringe2_10
  · exact fringe2_11
  · exact fringe2_12
  · exact fringe2_13
  · exact fringe2_14
  · exact fringe2_15
  · exact fringe2_16
  · exact fringe2_17
  · exact fringe2_18
  · exact fringe2_19
  · exact fringe2_20
  · exact fringe2_21
  · exact fringe2_22
  · exact fringe2_23
  · exact fringe2_24
  · exact fringe2_25
  · exact fringe2_26
  · exact fringe2_27
#print axioms fringeTable2_correct
end BurghartLists
