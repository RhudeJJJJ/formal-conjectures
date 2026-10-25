/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode204
import Proofs.RadenkovicGutmanD32Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[64,0],[0]],[[0,0],[0]],[[1024,0],[0]],[[0,0],[0]],[[6848,0],[0]],[[0,0],[0]],[[24832,0],[0]],[[0,0],[0]],[[52992,0],[0]],[[0,0],[0]],[[67584,64],[64]],[[0,0],[0]],[[49856,448],[448]],[[0,0],[0]],[[19200,1024],[1024]],[[0,0],[0]],[[2880,832],[832]],[[0,0],[0]],[[0,192],[192]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
