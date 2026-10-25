/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1587],[0,1587]],[[0,0,0],[0,0,0],[0,0]],[[0,14283,23805],[14283,76176,7015],[23805,7015]],[[0,0,0],[0,0,0],[0,0]],[[257094,886788,183747],[886788,569940,9062],[183747,9062]],[[0,0,0],[0,0,0],[0,0]],[[8934948,8324298,565202],[8324298,1700068,4439],[565202,4439]],[[0,0,0],[0,0,0],[0,0]],[[92362572,36041092,909029],[36041092,2666988,851],[909029,851]],[[0,0,0],[0,0,0],[0,0]],[[494359056,91105898,841018],[91105898,2424568,46],[841018,46]],[[0,0,0],[0,0],[0]],[[1650498078,148760642,462507],[148760642,1321028],[462507]],[[0,0,0],[0,0],[0]],[[3764397212,165263004,150098],[165263004,428996],[150098]],[[0,0,0],[0,0],[0]],[[6177517376,128328201,27071],[128328201,78660],[27071]],[[0,0,0],[0,0],[0]],[[7529360730,70405737,2277],[70405737,6992],[2277]],[[0,0,0],[0,0],[0]],[[6950932994,27214865,46],[27214865,184],[46]],[[0,0],[0]],[[4915345594,7279592],[7279592]],[[0,0],[0]],[[2674941768,1294831],[1294831]],[[0,0],[0]],[[1118739412,141450],[141450]],[[0,0],[0]],[[356780186,7981],[7981]],[[0,0],[0]],[[85398080,138],[138]],[[0]],[[14928656]],[[0]],[[1820450]],[[0]],[[142784]],[[0]],[[6118]],[[0]],[[92]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
