/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode034
import Proofs.RadenkovicGutmanD45Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-135],[-135]],[[0,0],[0]],[[-2025,-585],[-585]],[[0,0],[0]],[[-13500,-720],[-720]],[[0,0],[0]],[[-35055,-315],[-315]],[[0,0],[0]],[[-47520,-45],[-45]],[[0]],[[-37260]],[[0]],[[-17460]],[[0]],[[-4815]],[[0]],[[-720]],[[0]],[[-45]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
