/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode059
import Proofs.RadenkovicGutmanD40Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,120],[120,-76]],[[0,0],[0]],[[1116,-164],[-164]],[[0,0],[0]],[[-84,-1184],[-1184]],[[0,0],[0]],[[-21812,-1392],[-1392]],[[0,0],[0]],[[-66440,-568],[-568]],[[0,0],[0]],[[-91824,-76],[-76]],[[0]],[[-70816]],[[0]],[[-32276]],[[0]],[[-8632]],[[0]],[[-1252]],[[0]],[[-76]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
