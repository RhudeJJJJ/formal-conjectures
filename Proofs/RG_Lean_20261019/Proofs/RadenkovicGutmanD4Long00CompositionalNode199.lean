/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode196
import Proofs.RadenkovicGutmanD4Long00CompositionalNode198
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e199 : NestedArithmetic.Expr 3 := .plus e196 e198
noncomputable def p199 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[54,0],[0,0]],[[0,0],[0,0]],[[544,0],[0,0]],[[0,0],[0,0]],[[2842,0],[0,0]],[[0,0],[0,0]],[[8652,0],[0,0]],[[0,0],[0,0]],[[16008,2],[2,0]],[[0,0],[0,0]],[[17996,28],[28,0]],[[0,0],[0,0]],[[11802,132],[132,0]],[[0,0],[0,0]],[[4010,264],[264,0]],[[0,0],[0,0]],[[462,218],[218,0]],[[0,0],[0,0]],[[-36,60],[60,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step199 : p199=NestedHorner.add p196 p198 := by decide +kernel
#print axioms step199
theorem h199 : NestedArithmetic.compile e199=p199 := StagedExprCompile.compile_plus e199 e196 e198 p196 p198 p199 rfl h196 h198 step199
#print axioms h199
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
