/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode119
import Proofs.RadenkovicGutmanD14Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-352,0],[0,0]],[[0,0],[0,0]],[[-2144,0],[0,0]],[[0,0],[0,0]],[[-7008,0],[0,0]],[[0,0],[0,0]],[[-13264,0],[0,0]],[[0,0],[0,0]],[[-14592,-24],[-24,0]],[[0,0],[0,0]],[[-8672,-192],[-192,0]],[[0,0],[0,0]],[[-1888,-528],[-528,0]],[[0,0],[0,0]],[[552,-576],[-576,0]],[[0,0],[0,0]],[[288,-216],[-216,0]],[[0],[0,0]],[[0],[0,-24]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
