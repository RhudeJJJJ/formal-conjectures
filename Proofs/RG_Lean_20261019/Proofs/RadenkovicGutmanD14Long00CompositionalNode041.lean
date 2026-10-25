/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode036
import Proofs.RadenkovicGutmanD14Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-24]],[[0,0],[0]],[[288,-216],[-216]],[[0,0],[0]],[[552,-576],[-576]],[[0,0],[0]],[[-1888,-528],[-528]],[[0,0],[0]],[[-8672,-192],[-192]],[[0,0],[0]],[[-14592,-24],[-24]],[[0]],[[-13264]],[[0]],[[-7008]],[[0]],[[-2144]],[[0]],[[-352]],[[0]],[[-24]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
