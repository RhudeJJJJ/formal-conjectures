/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode044
import Proofs.RadenkovicGutmanD23Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,23]],[[0,0],[0,0]],[[207,207],[207,2]],[[0,0],[0]],[[3675,570],[570]],[[0,0],[0]],[[16349,554],[554]],[[0,0],[0]],[[34284,228],[228]],[[0,0],[0]],[[40672,39],[39]],[[0,0],[0]],[[29416,2],[2]],[[0]],[[13335]],[[0]],[[3768]],[[0]],[[635]],[[0]],[[57]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
