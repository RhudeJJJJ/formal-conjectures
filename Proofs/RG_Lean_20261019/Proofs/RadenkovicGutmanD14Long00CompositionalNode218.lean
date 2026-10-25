/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode034
import Proofs.RadenkovicGutmanD14Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-224,0],[0]],[[0,0],[0]],[[-1498,0],[0]],[[0,0],[0]],[[-5432,0],[0]],[[0,0],[0]],[[-11592,0],[0]],[[0,0],[0]],[[-14784,-14],[-14]],[[0,0],[0]],[[-10906,-98],[-98]],[[0,0],[0]],[[-4200,-224],[-224]],[[0,0],[0]],[[-630,-182],[-182]],[[0,0],[0]],[[0,-42],[-42]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
