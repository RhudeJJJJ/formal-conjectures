/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode065
import Proofs.RadenkovicGutmanD10Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-64,0],[0,0]],[[0,0],[0,0]],[[-734,0],[0,0]],[[0,0],[0,0]],[[-4322,0],[0,0]],[[0,0],[0,0]],[[-14842,0],[0,0]],[[0,0],[0,0]],[[-31208,-2],[-2,0]],[[0,0],[0,0]],[[-40420,-46],[-46,0]],[[0,0],[0,0]],[[-31274,-264],[-264,0]],[[0,0],[0,0]],[[-13288,-588],[-588,0]],[[0,0],[0,0]],[[-2508,-518],[-518,0]],[[0,0],[0,0]],[[-90,-150],[-150,-2]],[[0],[0,0]],[[0],[0,-10]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
