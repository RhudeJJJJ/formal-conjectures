/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode065
import Proofs.RadenkovicGutmanD8Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-58,0],[0,0]],[[0,0],[0,0]],[[-636,0],[0,0]],[[0,0],[0,0]],[[-3650,0],[0,0]],[[0,0],[0,0]],[[-12328,0],[0,0]],[[0,0],[0,0]],[[-25624,-2],[-2,0]],[[0,0],[0,0]],[[-32908,-40],[-40,0]],[[0,0],[0,0]],[[-25298,-220],[-220,0]],[[0,0],[0,0]],[[-10694,-480],[-480,0]],[[0,0],[0,0]],[[-2010,-418],[-418,0]],[[0,0],[0,0]],[[-72,-120],[-120,-2]],[[0],[0,0]],[[0],[0,-8]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
