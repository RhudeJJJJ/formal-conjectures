/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode034
import Proofs.RadenkovicGutmanD40Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-120],[-120]],[[0,0],[0]],[[-1800,-520],[-520]],[[0,0],[0]],[[-12000,-640],[-640]],[[0,0],[0]],[[-31160,-280],[-280]],[[0,0],[0]],[[-42240,-40],[-40]],[[0]],[[-33120]],[[0]],[[-15520]],[[0]],[[-4280]],[[0]],[[-640]],[[0]],[[-40]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
