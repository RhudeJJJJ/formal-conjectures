/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode045
import Proofs.RadenkovicGutmanD39Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,39]],[[0,0],[0,0]],[[-351,585],[585,2]],[[0,0],[0]],[[4311,1968],[1968]],[[0,0],[0]],[[36003,2154],[2154]],[[0,0],[0]],[[101812,902],[902]],[[0,0],[0]],[[148604,133],[133]],[[0,0],[0]],[[125532,2],[2]],[[0]],[[63477]],[[0]],[[18968]],[[0]],[[3113]],[[0]],[[225]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
