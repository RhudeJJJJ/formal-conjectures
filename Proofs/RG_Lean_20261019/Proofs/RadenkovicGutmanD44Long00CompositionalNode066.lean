/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode065
import Proofs.RadenkovicGutmanD44Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-44]],[[0,0],[0,0]],[[-396,-660],[-660,-2]],[[0,0],[0]],[[-10974,-2218],[-2218]],[[0,0],[0]],[[-57386,-2424],[-2424]],[[0,0],[0]],[[-132866,-1012],[-1012]],[[0,0],[0]],[[-168124,-148],[-148]],[[0,0],[0]],[[-126136,-2],[-2]],[[0]],[[-57580]],[[0]],[[-15746]],[[0]],[[-2400]],[[0]],[[-166]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
