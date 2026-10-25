/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode030
import Proofs.RadenkovicGutmanD37Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[37],[0]],[[0,0],[0]],[[555,0],[0,0]],[[0,0],[0,0]],[[3478,0],[0,0]],[[0,0],[0,0]],[[11803,0],[0,0]],[[0,0],[0,0]],[[23532,0],[0,0]],[[0,0],[0,0]],[[27972,37],[37,0]],[[0,0],[0,0]],[[19018,296],[296,0]],[[0,0],[0,0]],[[6179,814],[814,0]],[[0,0],[0,0]],[[111,888],[888,0]],[[0,0],[0,0]],[[-333,333],[333,0]],[[0],[0,0]],[[0],[0,37]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
