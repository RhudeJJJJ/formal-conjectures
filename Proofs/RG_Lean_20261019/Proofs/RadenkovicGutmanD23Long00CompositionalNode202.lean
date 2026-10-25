/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode191
import Proofs.RadenkovicGutmanD23Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[57,0],[0,0]],[[0,0],[0,0]],[[635,0],[0,0]],[[0,0],[0,0]],[[3768,0],[0,0]],[[0,0],[0,0]],[[13335,0],[0,0]],[[0,0],[0,0]],[[29416,2],[2,0]],[[0,0],[0,0]],[[40672,39],[39,0]],[[0,0],[0,0]],[[34284,228],[228,0]],[[0,0],[0,0]],[[16349,554],[554,0]],[[0,0],[0,0]],[[3675,570],[570,0]],[[0,0],[0,0]],[[207,207],[207,2]],[[0],[0,0]],[[0],[0,23]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
