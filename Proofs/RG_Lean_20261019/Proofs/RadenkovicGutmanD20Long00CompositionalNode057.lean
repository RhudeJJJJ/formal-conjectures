/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode034
import Proofs.RadenkovicGutmanD20Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-60],[-60]],[[0,0],[0]],[[-900,-260],[-260]],[[0,0],[0]],[[-6000,-320],[-320]],[[0,0],[0]],[[-15580,-140],[-140]],[[0,0],[0]],[[-21120,-20],[-20]],[[0]],[[-16560]],[[0]],[[-7760]],[[0]],[[-2140]],[[0]],[[-320]],[[0]],[[-20]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
