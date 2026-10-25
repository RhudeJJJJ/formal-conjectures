/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode191
import Proofs.RadenkovicGutmanD14Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[44,0],[0,0]],[[0,0],[0,0]],[[398,0],[0,0]],[[0,0],[0,0]],[[1954,0],[0,0]],[[0,0],[0,0]],[[5738,0],[0,0]],[[0,0],[0,0]],[[10416,2],[2,0]],[[0,0],[0,0]],[[11612,30],[30,0]],[[0,0],[0,0]],[[7530,156],[156,0]],[[0,0],[0,0]],[[2344,356],[356,0]],[[0,0],[0,0]],[[24,354],[354,0]],[[0,0],[0,0]],[[-126,126],[126,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
