/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode177
import Proofs.RadenkovicGutmanD36Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-68],[0]],[[0,0],[0]],[[-1156,0],[0,0]],[[0,0],[0,0]],[[-8296,0],[0,0]],[[0,0],[0,0]],[[-32708,0],[0,0]],[[0,0],[0,0]],[[-77248,0],[0,0]],[[0,0],[0,0]],[[-111792,-68],[-68,0]],[[0,0],[0,0]],[[-97240,-544],[-544,0]],[[0,0],[0,0]],[[-47396,-1496],[-1496,0]],[[0,0],[0,0]],[[-10812,-1632],[-1632,0]],[[0,0],[0,0]],[[-612,-612],[-612,0]],[[0],[0,0]],[[0],[0,-68]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
