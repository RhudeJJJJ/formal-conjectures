/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode195
import Proofs.RadenkovicGutmanD15Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[60,0],[0]],[[0,0],[0]],[[900,0],[0]],[[0,0],[0]],[[5640,0],[0]],[[0,0],[0]],[[19140,0],[0]],[[0,0],[0]],[[38160,0],[0]],[[0,0],[0]],[[45420,30],[30]],[[0,0],[0]],[[31320,210],[210]],[[0,0],[0]],[[11340,480],[480]],[[0,0],[0]],[[1620,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
