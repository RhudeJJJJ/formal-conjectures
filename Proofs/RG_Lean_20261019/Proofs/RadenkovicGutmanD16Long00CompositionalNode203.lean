/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode202
import Proofs.RadenkovicGutmanD16Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[50,0],[0,0]],[[0,0],[0,0]],[[516,0],[0,0]],[[0,0],[0,0]],[[2914,0],[0,0]],[[0,0],[0,0]],[[9968,0],[0,0]],[[0,0],[0,0]],[[21464,2],[2,0]],[[0,0],[0,0]],[[29164,32],[32,0]],[[0,0],[0,0]],[[24274,172],[172,0]],[[0,0],[0,0]],[[11470,400],[400,0]],[[0,0],[0,0]],[[2562,402],[402,0]],[[0,0],[0,0]],[[144,144],[144,2]],[[0],[0,0]],[[0],[0,16]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
