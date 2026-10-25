/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode164
import Proofs.RadenkovicGutmanD14Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-352,0],[0,0]],[[0,0],[0,0]],[[-2144,0],[0,0]],[[0,0],[0,0]],[[-7008,0],[0,0]],[[0,0],[0,0]],[[-13264,0],[0,0]],[[0,0],[0,0]],[[-14592,-24],[-24,0]],[[0,0],[0,0]],[[-8672,-192],[-192,0]],[[0,0],[0,0]],[[-1888,-528],[-528,0]],[[0,0],[0,0]],[[552,-576],[-576,0]],[[0,0],[0,0]],[[288,-216],[-216,0]],[[0],[0,0]],[[0],[0,-24]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
