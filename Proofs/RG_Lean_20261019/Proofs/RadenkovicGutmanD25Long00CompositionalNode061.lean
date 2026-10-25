/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode059
import Proofs.RadenkovicGutmanD25Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,75],[75,-46]],[[0,0],[0]],[[711,-89],[-89]],[[0,0],[0]],[[186,-704],[-704]],[[0,0],[0]],[[-12587,-837],[-837]],[[0,0],[0]],[[-39380,-343],[-343]],[[0,0],[0]],[[-54924,-46],[-46]],[[0]],[[-42556]],[[0]],[[-19451]],[[0]],[[-5212]],[[0]],[[-757]],[[0]],[[-46]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
