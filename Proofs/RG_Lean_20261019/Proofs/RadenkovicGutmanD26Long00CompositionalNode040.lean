/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode038
import Proofs.RadenkovicGutmanD26Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-24]],[[0,0],[0]],[[252,-216],[-216]],[[0,0],[0]],[[240,-576],[-576]],[[0,0],[0]],[[-2948,-528],[-528]],[[0,0],[0]],[[-10504,-192],[-192]],[[0,0],[0]],[[-16368,-24],[-24]],[[0]],[[-14264]],[[0]],[[-7332]],[[0]],[[-2200]],[[0]],[[-356]],[[0]],[[-24]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
