/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode195
import Proofs.RadenkovicGutmanD37Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[148,0],[0]],[[0,0],[0]],[[2220,0],[0]],[[0,0],[0]],[[13912,0],[0]],[[0,0],[0]],[[47212,0],[0]],[[0,0],[0]],[[94128,0],[0]],[[0,0],[0]],[[112036,74],[74]],[[0,0],[0]],[[77256,518],[518]],[[0,0],[0]],[[27972,1184],[1184]],[[0,0],[0]],[[3996,962],[962]],[[0,0],[0]],[[0,222],[222]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
