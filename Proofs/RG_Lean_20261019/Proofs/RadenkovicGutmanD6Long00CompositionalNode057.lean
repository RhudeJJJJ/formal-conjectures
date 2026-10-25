/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode034
import Proofs.RadenkovicGutmanD6Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-18],[-18]],[[0,0],[0]],[[-270,-78],[-78]],[[0,0],[0]],[[-1800,-96],[-96]],[[0,0],[0]],[[-4674,-42],[-42]],[[0,0],[0]],[[-6336,-6],[-6]],[[0]],[[-4968]],[[0]],[[-2328]],[[0]],[[-642]],[[0]],[[-96]],[[0]],[[-6]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
