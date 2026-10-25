/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode030
import Proofs.RadenkovicGutmanD40Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[40],[0]],[[0,0],[0]],[[600,0],[0,0]],[[0,0],[0,0]],[[3760,0],[0,0]],[[0,0],[0,0]],[[12760,0],[0,0]],[[0,0],[0,0]],[[25440,0],[0,0]],[[0,0],[0,0]],[[30240,40],[40,0]],[[0,0],[0,0]],[[20560,320],[320,0]],[[0,0],[0,0]],[[6680,880],[880,0]],[[0,0],[0,0]],[[120,960],[960,0]],[[0,0],[0,0]],[[-360,360],[360,0]],[[0],[0,0]],[[0],[0,40]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
