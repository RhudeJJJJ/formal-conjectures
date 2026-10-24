/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode006
import Proofs.RadenkovicGutmanD4Long00CompositionalNode154
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e179 : NestedArithmetic.Expr 3 := .times e006 e154
noncomputable def p179 : NestedHorner.Poly 3 := [[[1]],[[0]],[[14]],[[0]],[[81]],[[0]],[[250]],[[0]],[[444]],[[0]],[[458]],[[0]],[[265]],[[0]],[[78]],[[0]],[[9]]]
theorem step179 : p179=NestedArithmetic.mul p006 p154 := by decide +kernel
#print axioms step179
theorem h179 : NestedArithmetic.compile e179=p179 := StagedExprCompile.compile_times e179 e006 e154 p006 p154 p179 rfl h006 h154 step179
#print axioms h179
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
