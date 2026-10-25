/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode030
import Proofs.RadenkovicGutmanD37Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,37]],[[0,0],[0]],[[-333,333],[333]],[[0,0],[0]],[[111,888],[888]],[[0,0],[0]],[[6179,814],[814]],[[0,0],[0]],[[19018,296],[296]],[[0,0],[0]],[[27972,37],[37]],[[0]],[[23532]],[[0]],[[11803]],[[0]],[[3478]],[[0]],[[555]],[[0]],[[37]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
