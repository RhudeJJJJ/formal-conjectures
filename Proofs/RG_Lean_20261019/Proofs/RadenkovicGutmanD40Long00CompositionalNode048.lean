/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode047
import Proofs.RadenkovicGutmanD40Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,240],[240]],[[0,0],[0]],[[4320,1040],[1040]],[[0,0],[0]],[[30240,1280],[1280]],[[0,0],[0]],[[83520,560],[560]],[[0,0],[0]],[[121120,80],[80]],[[0]],[[101760]],[[0]],[[51040]],[[0]],[[15040]],[[0]],[[2400]],[[0]],[[160]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
