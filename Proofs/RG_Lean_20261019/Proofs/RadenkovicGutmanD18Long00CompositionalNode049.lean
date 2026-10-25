/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode045
import Proofs.RadenkovicGutmanD18Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,18]],[[0,0],[0,0]],[[-162,270],[270,2]],[[0,0],[0]],[[1980,918],[918]],[[0,0],[0]],[[16620,1020],[1020]],[[0,0],[0]],[[47170,440],[440]],[[0,0],[0]],[[69140,70],[70]],[[0,0],[0]],[[58752,2],[2]],[[0]],[[29982]],[[0]],[[9098]],[[0]],[[1538]],[[0]],[[120]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
