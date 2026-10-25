/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode160
import Proofs.RadenkovicGutmanD26Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-356,0],[0,0]],[[0,0],[0,0]],[[-2200,0],[0,0]],[[0,0],[0,0]],[[-7332,0],[0,0]],[[0,0],[0,0]],[[-14264,0],[0,0]],[[0,0],[0,0]],[[-16368,-24],[-24,0]],[[0,0],[0,0]],[[-10504,-192],[-192,0]],[[0,0],[0,0]],[[-2948,-528],[-528,0]],[[0,0],[0,0]],[[240,-576],[-576,0]],[[0,0],[0,0]],[[252,-216],[-216,0]],[[0],[0,0]],[[0],[0,-24]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
