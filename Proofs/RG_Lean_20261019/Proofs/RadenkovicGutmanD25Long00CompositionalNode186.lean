/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode178
import Proofs.RadenkovicGutmanD25Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-46],[0]],[[0,0],[0]],[[-757,0],[0,0]],[[0,0],[0,0]],[[-5212,0],[0,0]],[[0,0],[0,0]],[[-19451,0],[0,0]],[[0,0],[0,0]],[[-42556,0],[0,0]],[[0,0],[0,0]],[[-54924,-46],[-46,0]],[[0,0],[0,0]],[[-39380,-343],[-343,0]],[[0,0],[0,0]],[[-12587,-837],[-837,0]],[[0,0],[0,0]],[[186,-704],[-704,0]],[[0,0],[0,0]],[[711,-89],[-89,0]],[[0,0],[0,0]],[[0,75],[75,-46]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
