/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode065
import Proofs.RadenkovicGutmanD31Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-31]],[[0,0],[0,0]],[[-279,-465],[-465,-2]],[[0,0],[0]],[[-7737,-1568],[-1568]],[[0,0],[0]],[[-40525,-1722],[-1722]],[[0,0],[0]],[[-94022,-726],[-726]],[[0,0],[0]],[[-119296,-109],[-109]],[[0,0],[0]],[[-89840,-2],[-2]],[[0]],[[-41239]],[[0]],[[-11378]],[[0]],[[-1763]],[[0]],[[-127]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
