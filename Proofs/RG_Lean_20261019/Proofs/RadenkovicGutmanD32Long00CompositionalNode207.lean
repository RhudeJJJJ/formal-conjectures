/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode065
import Proofs.RadenkovicGutmanD32Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-130,0],[0,0]],[[0,0],[0,0]],[[-1812,0],[0,0]],[[0,0],[0,0]],[[-11714,0],[0,0]],[[0,0],[0,0]],[[-42496,0],[0,0]],[[0,0],[0,0]],[[-92632,-2],[-2,0]],[[0,0],[0,0]],[[-123052,-112],[-112,0]],[[0,0],[0,0]],[[-97010,-748],[-748,0]],[[0,0],[0,0]],[[-41822,-1776],[-1776,0]],[[0,0],[0,0]],[[-7986,-1618],[-1618,0]],[[0,0],[0,0]],[[-288,-480],[-480,-2]],[[0],[0,0]],[[0],[0,-32]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
