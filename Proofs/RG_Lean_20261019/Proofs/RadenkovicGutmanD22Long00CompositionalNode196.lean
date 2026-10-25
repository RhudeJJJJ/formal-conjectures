/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode195
import Proofs.RadenkovicGutmanD22Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[88,0],[0]],[[0,0],[0]],[[1320,0],[0]],[[0,0],[0]],[[8272,0],[0]],[[0,0],[0]],[[28072,0],[0]],[[0,0],[0]],[[55968,0],[0]],[[0,0],[0]],[[66616,44],[44]],[[0,0],[0]],[[45936,308],[308]],[[0,0],[0]],[[16632,704],[704]],[[0,0],[0]],[[2376,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
