/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode030
import Proofs.RadenkovicGutmanD45Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,45]],[[0,0],[0]],[[-405,405],[405]],[[0,0],[0]],[[135,1080],[1080]],[[0,0],[0]],[[7515,990],[990]],[[0,0],[0]],[[23130,360],[360]],[[0,0],[0]],[[34020,45],[45]],[[0]],[[28620]],[[0]],[[14355]],[[0]],[[4230]],[[0]],[[675]],[[0]],[[45]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
