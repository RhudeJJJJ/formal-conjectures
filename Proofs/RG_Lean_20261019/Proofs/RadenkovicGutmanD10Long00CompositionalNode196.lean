/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode195
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[40,0],[0]],[[0,0],[0]],[[600,0],[0]],[[0,0],[0]],[[3760,0],[0]],[[0,0],[0]],[[12760,0],[0]],[[0,0],[0]],[[25440,0],[0]],[[0,0],[0]],[[30280,20],[20]],[[0,0],[0]],[[20880,140],[140]],[[0,0],[0]],[[7560,320],[320]],[[0,0],[0]],[[1080,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
