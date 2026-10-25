/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode030
import Proofs.RadenkovicGutmanD43Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[43],[0]],[[0,0],[0]],[[645,0],[0,0]],[[0,0],[0,0]],[[4042,0],[0,0]],[[0,0],[0,0]],[[13717,0],[0,0]],[[0,0],[0,0]],[[27348,0],[0,0]],[[0,0],[0,0]],[[32508,43],[43,0]],[[0,0],[0,0]],[[22102,344],[344,0]],[[0,0],[0,0]],[[7181,946],[946,0]],[[0,0],[0,0]],[[129,1032],[1032,0]],[[0,0],[0,0]],[[-387,387],[387,0]],[[0],[0,0]],[[0],[0,43]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
