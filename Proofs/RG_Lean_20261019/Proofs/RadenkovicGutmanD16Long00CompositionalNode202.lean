/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode191
import Proofs.RadenkovicGutmanD16Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[50,0],[0,0]],[[0,0],[0,0]],[[516,0],[0,0]],[[0,0],[0,0]],[[2914,0],[0,0]],[[0,0],[0,0]],[[9968,0],[0,0]],[[0,0],[0,0]],[[21464,2],[2,0]],[[0,0],[0,0]],[[29164,32],[32,0]],[[0,0],[0,0]],[[24274,172],[172,0]],[[0,0],[0,0]],[[11470,400],[400,0]],[[0,0],[0,0]],[[2562,402],[402,0]],[[0,0],[0,0]],[[144,144],[144,2]],[[0],[0,0]],[[0],[0,16]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
