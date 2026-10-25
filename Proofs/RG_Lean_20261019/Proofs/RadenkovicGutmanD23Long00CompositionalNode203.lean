/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode202
import Proofs.RadenkovicGutmanD23Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[57,0],[0,0]],[[0,0],[0,0]],[[635,0],[0,0]],[[0,0],[0,0]],[[3768,0],[0,0]],[[0,0],[0,0]],[[13335,0],[0,0]],[[0,0],[0,0]],[[29416,2],[2,0]],[[0,0],[0,0]],[[40672,39],[39,0]],[[0,0],[0,0]],[[34284,228],[228,0]],[[0,0],[0,0]],[[16349,554],[554,0]],[[0,0],[0,0]],[[3675,570],[570,0]],[[0,0],[0,0]],[[207,207],[207,2]],[[0],[0,0]],[[0],[0,23]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
