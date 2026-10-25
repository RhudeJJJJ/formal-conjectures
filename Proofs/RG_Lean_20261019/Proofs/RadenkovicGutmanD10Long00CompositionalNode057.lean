/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode034
import Proofs.RadenkovicGutmanD10Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-30],[-30]],[[0,0],[0]],[[-450,-130],[-130]],[[0,0],[0]],[[-3000,-160],[-160]],[[0,0],[0]],[[-7790,-70],[-70]],[[0,0],[0]],[[-10560,-10],[-10]],[[0]],[[-8280]],[[0]],[[-3880]],[[0]],[[-1070]],[[0]],[[-160]],[[0]],[[-10]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
