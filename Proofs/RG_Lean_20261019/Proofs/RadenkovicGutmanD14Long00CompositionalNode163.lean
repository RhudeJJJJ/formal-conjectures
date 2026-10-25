/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode160
import Proofs.RadenkovicGutmanD14Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-176,0],[0,0]],[[0,0],[0,0]],[[-1072,0],[0,0]],[[0,0],[0,0]],[[-3504,0],[0,0]],[[0,0],[0,0]],[[-6632,0],[0,0]],[[0,0],[0,0]],[[-7296,-12],[-12,0]],[[0,0],[0,0]],[[-4336,-96],[-96,0]],[[0,0],[0,0]],[[-944,-264],[-264,0]],[[0,0],[0,0]],[[276,-288],[-288,0]],[[0,0],[0,0]],[[144,-108],[-108,0]],[[0],[0,0]],[[0],[0,-12]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
