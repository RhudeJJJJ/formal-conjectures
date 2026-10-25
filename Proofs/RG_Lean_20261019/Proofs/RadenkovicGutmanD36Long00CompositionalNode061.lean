/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode059
import Proofs.RadenkovicGutmanD36Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,108],[108,-68]],[[0,0],[0]],[[1008,-144],[-144]],[[0,0],[0]],[[-12,-1056],[-1056]],[[0,0],[0]],[[-19352,-1244],[-1244]],[[0,0],[0]],[[-59224,-508],[-508]],[[0,0],[0]],[[-81984,-68],[-68]],[[0]],[[-63280]],[[0]],[[-28856]],[[0]],[[-7720]],[[0]],[[-1120]],[[0]],[[-68]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
