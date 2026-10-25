/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode034
import Proofs.RadenkovicGutmanD14Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-42],[-42]],[[0,0],[0]],[[-630,-182],[-182]],[[0,0],[0]],[[-4200,-224],[-224]],[[0,0],[0]],[[-10906,-98],[-98]],[[0,0],[0]],[[-14784,-14],[-14]],[[0]],[[-11592]],[[0]],[[-5432]],[[0]],[[-1498]],[[0]],[[-224]],[[0]],[[-14]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
