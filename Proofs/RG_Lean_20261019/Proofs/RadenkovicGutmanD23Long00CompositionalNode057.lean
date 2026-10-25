/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode034
import Proofs.RadenkovicGutmanD23Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-69],[-69]],[[0,0],[0]],[[-1035,-299],[-299]],[[0,0],[0]],[[-6900,-368],[-368]],[[0,0],[0]],[[-17917,-161],[-161]],[[0,0],[0]],[[-24288,-23],[-23]],[[0]],[[-19044]],[[0]],[[-8924]],[[0]],[[-2461]],[[0]],[[-368]],[[0]],[[-23]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
