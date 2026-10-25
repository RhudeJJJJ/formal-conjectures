/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode034
import Proofs.RadenkovicGutmanD42Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-126],[-126]],[[0,0],[0]],[[-1890,-546],[-546]],[[0,0],[0]],[[-12600,-672],[-672]],[[0,0],[0]],[[-32718,-294],[-294]],[[0,0],[0]],[[-44352,-42],[-42]],[[0]],[[-34776]],[[0]],[[-16296]],[[0]],[[-4494]],[[0]],[[-672]],[[0]],[[-42]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
