/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode044
import Proofs.RadenkovicGutmanD16Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,16]],[[0,0],[0,0]],[[144,144],[144,2]],[[0,0],[0]],[[2562,402],[402]],[[0,0],[0]],[[11470,400],[400]],[[0,0],[0]],[[24274,172],[172]],[[0,0],[0]],[[29164,32],[32]],[[0,0],[0]],[[21464,2],[2]],[[0]],[[9968]],[[0]],[[2914]],[[0]],[[516]],[[0]],[[50]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
