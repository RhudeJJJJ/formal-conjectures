/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode030
import Proofs.RadenkovicGutmanD28Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[28],[0]],[[0,0],[0]],[[420,0],[0,0]],[[0,0],[0,0]],[[2632,0],[0,0]],[[0,0],[0,0]],[[8932,0],[0,0]],[[0,0],[0,0]],[[17808,0],[0,0]],[[0,0],[0,0]],[[21168,28],[28,0]],[[0,0],[0,0]],[[14392,224],[224,0]],[[0,0],[0,0]],[[4676,616],[616,0]],[[0,0],[0,0]],[[84,672],[672,0]],[[0,0],[0,0]],[[-252,252],[252,0]],[[0],[0,0]],[[0],[0,28]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
