/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode192
import Proofs.RadenkovicGutmanD14Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[44,0],[0,0]],[[0,0],[0,0]],[[398,0],[0,0]],[[0,0],[0,0]],[[1954,0],[0,0]],[[0,0],[0,0]],[[5738,0],[0,0]],[[0,0],[0,0]],[[10416,2],[2,0]],[[0,0],[0,0]],[[11612,30],[30,0]],[[0,0],[0,0]],[[7530,156],[156,0]],[[0,0],[0,0]],[[2344,356],[356,0]],[[0,0],[0,0]],[[24,354],[354,0]],[[0,0],[0,0]],[[-126,126],[126,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
