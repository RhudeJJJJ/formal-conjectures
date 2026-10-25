/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode034
import Proofs.RadenkovicGutmanD22Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-352,0],[0]],[[0,0],[0]],[[-2354,0],[0]],[[0,0],[0]],[[-8536,0],[0]],[[0,0],[0]],[[-18216,0],[0]],[[0,0],[0]],[[-23232,-22],[-22]],[[0,0],[0]],[[-17138,-154],[-154]],[[0,0],[0]],[[-6600,-352],[-352]],[[0,0],[0]],[[-990,-286],[-286]],[[0,0],[0]],[[0,-66],[-66]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
