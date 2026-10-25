/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode197
import Proofs.RadenkovicGutmanD39Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[225,0],[0,0]],[[0,0],[0,0]],[[3113,0],[0,0]],[[0,0],[0,0]],[[18968,0],[0,0]],[[0,0],[0,0]],[[63477,0],[0,0]],[[0,0],[0,0]],[[125532,2],[2,0]],[[0,0],[0,0]],[[148604,133],[133,0]],[[0,0],[0,0]],[[101812,902],[902,0]],[[0,0],[0,0]],[[36003,2154],[2154,0]],[[0,0],[0,0]],[[4311,1968],[1968,0]],[[0,0],[0,0]],[[-351,585],[585,2]],[[0],[0,0]],[[0],[0,39]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
