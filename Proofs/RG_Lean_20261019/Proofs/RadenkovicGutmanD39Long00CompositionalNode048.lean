/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode047
import Proofs.RadenkovicGutmanD39Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,234],[234]],[[0,0],[0]],[[4212,1014],[1014]],[[0,0],[0]],[[29484,1248],[1248]],[[0,0],[0]],[[81432,546],[546]],[[0,0],[0]],[[118092,78],[78]],[[0]],[[99216]],[[0]],[[49764]],[[0]],[[14664]],[[0]],[[2340]],[[0]],[[156]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
