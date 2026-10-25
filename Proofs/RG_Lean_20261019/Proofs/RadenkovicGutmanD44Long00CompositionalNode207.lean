/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode065
import Proofs.RadenkovicGutmanD44Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-166,0],[0,0]],[[0,0],[0,0]],[[-2400,0],[0,0]],[[0,0],[0,0]],[[-15746,0],[0,0]],[[0,0],[0,0]],[[-57580,0],[0,0]],[[0,0],[0,0]],[[-126136,-2],[-2,0]],[[0,0],[0,0]],[[-168124,-148],[-148,0]],[[0,0],[0,0]],[[-132866,-1012],[-1012,0]],[[0,0],[0,0]],[[-57386,-2424],[-2424,0]],[[0,0],[0,0]],[[-10974,-2218],[-2218,0]],[[0,0],[0,0]],[[-396,-660],[-660,-2]],[[0],[0,0]],[[0],[0,-44]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
