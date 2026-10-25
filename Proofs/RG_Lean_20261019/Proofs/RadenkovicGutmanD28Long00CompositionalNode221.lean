/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[1568],[0],[0]],[[0,0],[0,0],[0]],[[48608,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[691488,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[5983488,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[35195328,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[148981952,2352,0],[2352,0],[0]],[[0,0,0],[0,0],[0]],[[468689312,52528,0],[52528,0],[0]],[[0,0,0],[0,0],[0]],[[1115928352,521360,0],[521360,0],[0]],[[0,0,0],[0,0],[0]],[[2028778752,3030944,0],[3030944,0],[0]],[[0,0,0],[0,0],[0]],[[2820799072,11453456,0],[11453456,0],[0]],[[0,0,0],[0,0],[0]],[[2984222304,29524656,784],[29524656,1568],[784]],[[0,0,0],[0,0],[0]],[[2372474944,53026624,10976],[53026624,21952],[10976]],[[0,0,0],[0,0],[0]],[[1386579264,66590608,63504],[66590608,127008],[63504]],[[0,0,0],[0,0],[0]],[[574527744,57798832,196000],[57798832,392000],[196000]],[[0,0,0],[0,0],[0]],[[158717664,33672800,348096],[33672800,696192],[348096]],[[0,0,0],[0,0],[0]],[[26036640,12439728,359072],[12439728,718144],[359072]],[[0,0,0],[0,0],[0]],[[1905120,2603664,207760],[2603664,415520],[207760]],[[0,0,0],[0,0],[0]],[[0,232848,61152],[232848,122304],[61152]],[[0,0,0],[0,0],[0]],[[0,0,7056],[0,14112],[7056]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
