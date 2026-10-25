/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode034
import Proofs.RadenkovicGutmanD7Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-21],[-21]],[[0,0],[0]],[[-315,-91],[-91]],[[0,0],[0]],[[-2100,-112],[-112]],[[0,0],[0]],[[-5453,-49],[-49]],[[0,0],[0]],[[-7392,-7],[-7]],[[0]],[[-5796]],[[0]],[[-2716]],[[0]],[[-749]],[[0]],[[-112]],[[0]],[[-7]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
