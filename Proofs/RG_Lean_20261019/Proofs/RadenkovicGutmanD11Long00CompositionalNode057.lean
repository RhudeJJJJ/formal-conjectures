/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode034
import Proofs.RadenkovicGutmanD11Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-33],[-33]],[[0,0],[0]],[[-495,-143],[-143]],[[0,0],[0]],[[-3300,-176],[-176]],[[0,0],[0]],[[-8569,-77],[-77]],[[0,0],[0]],[[-11616,-11],[-11]],[[0]],[[-9108]],[[0]],[[-4268]],[[0]],[[-1177]],[[0]],[[-176]],[[0]],[[-11]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
