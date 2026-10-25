/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode044
import Proofs.RadenkovicGutmanD13Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,13]],[[0,0],[0,0]],[[-117,117],[117,2]],[[0,0],[0]],[[21,330],[330]],[[0,0],[0]],[[2177,334],[334]],[[0,0],[0]],[[7016,148],[148]],[[0,0],[0]],[[10856,29],[29]],[[0,0],[0]],[[9780,2],[2]],[[0]],[[5419]],[[0]],[[1860]],[[0]],[[383]],[[0]],[[43]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
