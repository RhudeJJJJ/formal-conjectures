/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode058
import Proofs.RadenkovicGutmanD36Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-68]],[[0,0],[0]],[[-612,-612],[-612]],[[0,0],[0]],[[-10812,-1632],[-1632]],[[0,0],[0]],[[-47396,-1496],[-1496]],[[0,0],[0]],[[-97240,-544],[-544]],[[0,0],[0]],[[-111792,-68],[-68]],[[0]],[[-77248]],[[0]],[[-32708]],[[0]],[[-8296]],[[0]],[[-1156]],[[0]],[[-68]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
