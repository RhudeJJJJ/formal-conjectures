/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode034
import Proofs.RadenkovicGutmanD15Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-45],[-45]],[[0,0],[0]],[[-675,-195],[-195]],[[0,0],[0]],[[-4500,-240],[-240]],[[0,0],[0]],[[-11685,-105],[-105]],[[0,0],[0]],[[-15840,-15],[-15]],[[0]],[[-12420]],[[0]],[[-5820]],[[0]],[[-1605]],[[0]],[[-240]],[[0]],[[-15]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
