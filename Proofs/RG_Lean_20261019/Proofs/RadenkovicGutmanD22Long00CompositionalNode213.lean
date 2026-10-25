/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode030
import Proofs.RadenkovicGutmanD22Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[22],[0]],[[0,0],[0]],[[330,0],[0,0]],[[0,0],[0,0]],[[2068,0],[0,0]],[[0,0],[0,0]],[[7018,0],[0,0]],[[0,0],[0,0]],[[13992,0],[0,0]],[[0,0],[0,0]],[[16632,22],[22,0]],[[0,0],[0,0]],[[11308,176],[176,0]],[[0,0],[0,0]],[[3674,484],[484,0]],[[0,0],[0,0]],[[66,528],[528,0]],[[0,0],[0,0]],[[-198,198],[198,0]],[[0],[0,0]],[[0],[0,22]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
