/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode195
import Proofs.RadenkovicGutmanD39Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[156,0],[0]],[[0,0],[0]],[[2340,0],[0]],[[0,0],[0]],[[14664,0],[0]],[[0,0],[0]],[[49764,0],[0]],[[0,0],[0]],[[99216,0],[0]],[[0,0],[0]],[[118092,78],[78]],[[0,0],[0]],[[81432,546],[546]],[[0,0],[0]],[[29484,1248],[1248]],[[0,0],[0]],[[4212,1014],[1014]],[[0,0],[0]],[[0,234],[234]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
