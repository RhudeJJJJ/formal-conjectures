/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode191
import Proofs.RadenkovicGutmanD13Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[43,0],[0,0]],[[0,0],[0,0]],[[383,0],[0,0]],[[0,0],[0,0]],[[1860,0],[0,0]],[[0,0],[0,0]],[[5419,0],[0,0]],[[0,0],[0,0]],[[9780,2],[2,0]],[[0,0],[0,0]],[[10856,29],[29,0]],[[0,0],[0,0]],[[7016,148],[148,0]],[[0,0],[0,0]],[[2177,334],[334,0]],[[0,0],[0,0]],[[21,330],[330,0]],[[0,0],[0,0]],[[-117,117],[117,2]],[[0],[0,0]],[[0],[0,13]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
