/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode198
import Proofs.RadenkovicGutmanD42Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[244,0],[0,0]],[[0,0],[0,0]],[[3394,0],[0,0]],[[0,0],[0,0]],[[20702,0],[0,0]],[[0,0],[0,0]],[[69262,0],[0,0]],[[0,0],[0,0]],[[136848,2],[2,0]],[[0,0],[0,0]],[[161788,142],[142,0]],[[0,0],[0,0]],[[110678,968],[968,0]],[[0,0],[0,0]],[[39084,2316],[2316,0]],[[0,0],[0,0]],[[4680,2118],[2118,0]],[[0,0],[0,0]],[[-378,630],[630,2]],[[0],[0,0]],[[0],[0,42]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
