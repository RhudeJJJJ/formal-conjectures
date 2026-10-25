/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode174
import Proofs.RadenkovicGutmanD36Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-68],[0]],[[0,0],[0]],[[-1156,0],[0,0]],[[0,0],[0,0]],[[-8296,0],[0,0]],[[0,0],[0,0]],[[-32708,0],[0,0]],[[0,0],[0,0]],[[-77248,0],[0,0]],[[0,0],[0,0]],[[-111792,-68],[-68,0]],[[0,0],[0,0]],[[-97240,-544],[-544,0]],[[0,0],[0,0]],[[-47396,-1496],[-1496,0]],[[0,0],[0,0]],[[-10812,-1632],[-1632,0]],[[0,0],[0,0]],[[-612,-612],[-612,0]],[[0],[0,0]],[[0],[0,-68]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
