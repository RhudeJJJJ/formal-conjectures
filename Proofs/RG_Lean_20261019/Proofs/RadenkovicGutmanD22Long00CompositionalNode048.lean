/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode047
import Proofs.RadenkovicGutmanD22Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,132],[132]],[[0,0],[0]],[[2376,572],[572]],[[0,0],[0]],[[16632,704],[704]],[[0,0],[0]],[[45936,308],[308]],[[0,0],[0]],[[66616,44],[44]],[[0]],[[55968]],[[0]],[[28072]],[[0]],[[8272]],[[0]],[[1320]],[[0]],[[88]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
