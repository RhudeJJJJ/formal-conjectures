/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode204
import Proofs.RadenkovicGutmanD34Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[68,0],[0]],[[0,0],[0]],[[1088,0],[0]],[[0,0],[0]],[[7276,0],[0]],[[0,0],[0]],[[26384,0],[0]],[[0,0],[0]],[[56304,0],[0]],[[0,0],[0]],[[71808,68],[68]],[[0,0],[0]],[[52972,476],[476]],[[0,0],[0]],[[20400,1088],[1088]],[[0,0],[0]],[[3060,884],[884]],[[0,0],[0]],[[0,204],[204]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
