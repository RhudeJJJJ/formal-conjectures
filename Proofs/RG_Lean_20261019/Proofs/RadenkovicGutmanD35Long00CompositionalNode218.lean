/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode034
import Proofs.RadenkovicGutmanD35Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-35],[0]],[[0,0],[0]],[[-560,0],[0]],[[0,0],[0]],[[-3745,0],[0]],[[0,0],[0]],[[-13580,0],[0]],[[0,0],[0]],[[-28980,0],[0]],[[0,0],[0]],[[-36960,-35],[-35]],[[0,0],[0]],[[-27265,-245],[-245]],[[0,0],[0]],[[-10500,-560],[-560]],[[0,0],[0]],[[-1575,-455],[-455]],[[0,0],[0]],[[0,-105],[-105]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
