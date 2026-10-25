/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode204
import Proofs.RadenkovicGutmanD28Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[56,0],[0]],[[0,0],[0]],[[896,0],[0]],[[0,0],[0]],[[5992,0],[0]],[[0,0],[0]],[[21728,0],[0]],[[0,0],[0]],[[46368,0],[0]],[[0,0],[0]],[[59136,56],[56]],[[0,0],[0]],[[43624,392],[392]],[[0,0],[0]],[[16800,896],[896]],[[0,0],[0]],[[2520,728],[728]],[[0,0],[0]],[[0,168],[168]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
