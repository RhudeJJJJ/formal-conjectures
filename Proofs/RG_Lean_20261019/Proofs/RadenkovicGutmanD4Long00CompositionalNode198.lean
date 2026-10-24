/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode197
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e003
noncomputable def p198 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step198 : p198=NestedArithmetic.mul p197 p003 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e003 p197 p003 p198 rfl h197 h003 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
