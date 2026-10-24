/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode044
import Proofs.RadenkovicGutmanD4Long00CompositionalNode047
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .plus e044 e047
noncomputable def p048 : NestedHorner.Poly 3 := [[[0],[0,4]],[[0,0],[0,0]],[[-36,60],[60,2]],[[0,0],[0]],[[426,218],[218]],[[0,0],[0]],[[3698,264],[264]],[[0,0],[0]],[[10742,132],[132]],[[0,0],[0]],[[16164,28],[28]],[[0,0],[0]],[[14232,2],[2]],[[0]],[[7652]],[[0]],[[2518]],[[0]],[[488]],[[0]],[[50]],[[0]],[[2]]]
theorem step048 : p048=NestedHorner.add p044 p047 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_plus e048 e044 e047 p044 p047 p048 rfl h044 h047 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
