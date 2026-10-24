/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode195
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e121
noncomputable def p196 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[50,0],[0,0]],[[0,0],[0,0]],[[488,0],[0,0]],[[0,0],[0,0]],[[2518,0],[0,0]],[[0,0],[0,0]],[[7652,0],[0,0]],[[0,0],[0,0]],[[14232,2],[2,0]],[[0,0],[0,0]],[[16164,28],[28,0]],[[0,0],[0,0]],[[10742,132],[132,0]],[[0,0],[0,0]],[[3698,264],[264,0]],[[0,0],[0,0]],[[426,218],[218,0]],[[0,0],[0,0]],[[-36,60],[60,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step196 : p196=NestedArithmetic.mul p195 p121 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e121 p195 p121 p196 rfl h195 h121 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
