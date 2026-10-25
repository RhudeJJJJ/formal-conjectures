/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode034
import Proofs.RadenkovicGutmanD27Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-81],[-81]],[[0,0],[0]],[[-1215,-351],[-351]],[[0,0],[0]],[[-8100,-432],[-432]],[[0,0],[0]],[[-21033,-189],[-189]],[[0,0],[0]],[[-28512,-27],[-27]],[[0]],[[-22356]],[[0]],[[-10476]],[[0]],[[-2889]],[[0]],[[-432]],[[0]],[[-27]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
