/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode047
import Proofs.RadenkovicGutmanD28Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,168],[168]],[[0,0],[0]],[[3024,728],[728]],[[0,0],[0]],[[21168,896],[896]],[[0,0],[0]],[[58464,392],[392]],[[0,0],[0]],[[84784,56],[56]],[[0]],[[71232]],[[0]],[[35728]],[[0]],[[10528]],[[0]],[[1680]],[[0]],[[112]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
