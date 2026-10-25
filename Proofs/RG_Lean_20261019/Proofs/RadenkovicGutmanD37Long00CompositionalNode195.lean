/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode194
import Proofs.RadenkovicGutmanD37Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[148],[0]],[[0,0],[0]],[[2220,0],[0]],[[0,0],[0]],[[13912,0],[0]],[[0,0],[0]],[[47212,0],[0]],[[0,0],[0]],[[94128,0],[0]],[[0,0],[0]],[[112036,74],[74]],[[0,0],[0]],[[77256,518],[518]],[[0,0],[0]],[[27972,1184],[1184]],[[0,0],[0]],[[3996,962],[962]],[[0,0],[0]],[[0,222],[222]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
