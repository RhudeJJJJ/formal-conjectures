/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode204
import Proofs.RadenkovicGutmanD12Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[24,0],[0]],[[0,0],[0]],[[384,0],[0]],[[0,0],[0]],[[2568,0],[0]],[[0,0],[0]],[[9312,0],[0]],[[0,0],[0]],[[19872,0],[0]],[[0,0],[0]],[[25344,24],[24]],[[0,0],[0]],[[18696,168],[168]],[[0,0],[0]],[[7200,384],[384]],[[0,0],[0]],[[1080,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
