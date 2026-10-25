/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode045
import Proofs.RadenkovicGutmanD36Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,36]],[[0,0],[0,0]],[[-324,540],[540,2]],[[0,0],[0]],[[3978,1818],[1818]],[[0,0],[0]],[[33234,1992],[1992]],[[0,0],[0]],[[94006,836],[836]],[[0,0],[0]],[[137252,124],[124]],[[0,0],[0]],[[115992,2],[2]],[[0]],[[58692]],[[0]],[[17558]],[[0]],[[2888]],[[0]],[[210]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
