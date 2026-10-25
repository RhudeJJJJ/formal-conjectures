/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode030
import Proofs.RadenkovicGutmanD7Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[7],[0]],[[0,0],[0]],[[105,0],[0,0]],[[0,0],[0,0]],[[658,0],[0,0]],[[0,0],[0,0]],[[2233,0],[0,0]],[[0,0],[0,0]],[[4452,0],[0,0]],[[0,0],[0,0]],[[5292,7],[7,0]],[[0,0],[0,0]],[[3598,56],[56,0]],[[0,0],[0,0]],[[1169,154],[154,0]],[[0,0],[0,0]],[[21,168],[168,0]],[[0,0],[0,0]],[[-63,63],[63,0]],[[0],[0,0]],[[0],[0,7]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
