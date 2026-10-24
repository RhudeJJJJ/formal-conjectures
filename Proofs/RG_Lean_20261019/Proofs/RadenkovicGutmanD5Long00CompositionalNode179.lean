/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode170
import Proofs.RadenkovicGutmanD5Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e179 : NestedArithmetic.Expr 3 := .times e170 e122
noncomputable def p179 : NestedHorner.Poly 3 := [[[2],[]],[[0,0],[0]],[[30,0],[0]],[[0,0],[0]],[[188,0],[0]],[[0,0],[0]],[[638,0],[0]],[[0,0],[0]],[[1272,0],[0]],[[0,0],[0]],[[1514,1],[1]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step179 : p179=NestedArithmetic.mul p170 p122 := by decide +kernel
#print axioms step179
theorem h179 : NestedArithmetic.compile e179=p179 := StagedExprCompile.compile_times e179 e170 e122 p170 p122 p179 rfl h170 h122 step179
#print axioms h179
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
