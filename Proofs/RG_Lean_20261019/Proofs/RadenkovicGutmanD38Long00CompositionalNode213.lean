/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode030
import Proofs.RadenkovicGutmanD38Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[38],[0]],[[0,0],[0]],[[570,0],[0,0]],[[0,0],[0,0]],[[3572,0],[0,0]],[[0,0],[0,0]],[[12122,0],[0,0]],[[0,0],[0,0]],[[24168,0],[0,0]],[[0,0],[0,0]],[[28728,38],[38,0]],[[0,0],[0,0]],[[19532,304],[304,0]],[[0,0],[0,0]],[[6346,836],[836,0]],[[0,0],[0,0]],[[114,912],[912,0]],[[0,0],[0,0]],[[-342,342],[342,0]],[[0],[0,0]],[[0],[0,38]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
