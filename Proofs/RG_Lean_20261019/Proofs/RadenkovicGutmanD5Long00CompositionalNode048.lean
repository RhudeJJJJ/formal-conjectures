/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode047
import Proofs.RadenkovicGutmanD5Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,30],[30]],[[0,0],[0]],[[540,130],[130]],[[0,0],[0]],[[3780,160],[160]],[[0,0],[0]],[[10440,70],[70]],[[0,0],[0]],[[15140,10],[10]],[[0]],[[12720]],[[0]],[[6380]],[[0]],[[1880]],[[0]],[[300]],[[0]],[[20]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
