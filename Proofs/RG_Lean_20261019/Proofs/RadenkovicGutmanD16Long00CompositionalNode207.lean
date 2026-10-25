/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode065
import Proofs.RadenkovicGutmanD16Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-82,0],[0,0]],[[0,0],[0,0]],[[-1028,0],[0,0]],[[0,0],[0,0]],[[-6338,0],[0,0]],[[0,0],[0,0]],[[-22384,0],[0,0]],[[0,0],[0,0]],[[-47960,-2],[-2,0]],[[0,0],[0,0]],[[-62956,-64],[-64,0]],[[0,0],[0,0]],[[-49202,-396],[-396,0]],[[0,0],[0,0]],[[-21070,-912],[-912,0]],[[0,0],[0,0]],[[-4002,-818],[-818,0]],[[0,0],[0,0]],[[-144,-240],[-240,-2]],[[0],[0,0]],[[0],[0,-16]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
