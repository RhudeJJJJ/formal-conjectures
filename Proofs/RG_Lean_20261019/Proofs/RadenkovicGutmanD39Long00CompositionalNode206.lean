/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode203
import Proofs.RadenkovicGutmanD39Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[151,0],[0,0]],[[0,0],[0,0]],[[2155,0],[0,0]],[[0,0],[0,0]],[[14066,0],[0,0]],[[0,0],[0,0]],[[51295,0],[0,0]],[[0,0],[0,0]],[[112176,2],[2,0]],[[0,0],[0,0]],[[149344,133],[133,0]],[[0,0],[0,0]],[[117926,902],[902,0]],[[0,0],[0,0]],[[50901,2154],[2154,0]],[[0,0],[0,0]],[[9729,1968],[1968,0]],[[0,0],[0,0]],[[351,585],[585,2]],[[0],[0,0]],[[0],[0,39]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
