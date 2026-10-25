/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode192
import Proofs.RadenkovicGutmanD13Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[43,0],[0,0]],[[0,0],[0,0]],[[383,0],[0,0]],[[0,0],[0,0]],[[1860,0],[0,0]],[[0,0],[0,0]],[[5419,0],[0,0]],[[0,0],[0,0]],[[9780,2],[2,0]],[[0,0],[0,0]],[[10856,29],[29,0]],[[0,0],[0,0]],[[7016,148],[148,0]],[[0,0],[0,0]],[[2177,334],[334,0]],[[0,0],[0,0]],[[21,330],[330,0]],[[0,0],[0,0]],[[-117,117],[117,2]],[[0],[0,0]],[[0],[0,13]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
