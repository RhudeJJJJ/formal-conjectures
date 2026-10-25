/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode047
import Proofs.RadenkovicGutmanD44Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,264],[264]],[[0,0],[0]],[[4752,1144],[1144]],[[0,0],[0]],[[33264,1408],[1408]],[[0,0],[0]],[[91872,616],[616]],[[0,0],[0]],[[133232,88],[88]],[[0]],[[111936]],[[0]],[[56144]],[[0]],[[16544]],[[0]],[[2640]],[[0]],[[176]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
