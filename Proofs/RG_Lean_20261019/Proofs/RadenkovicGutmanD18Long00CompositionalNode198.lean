/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode197
import Proofs.RadenkovicGutmanD18Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[120,0],[0,0]],[[0,0],[0,0]],[[1538,0],[0,0]],[[0,0],[0,0]],[[9098,0],[0,0]],[[0,0],[0,0]],[[29982,0],[0,0]],[[0,0],[0,0]],[[58752,2],[2,0]],[[0,0],[0,0]],[[69140,70],[70,0]],[[0,0],[0,0]],[[47170,440],[440,0]],[[0,0],[0,0]],[[16620,1020],[1020,0]],[[0,0],[0,0]],[[1980,918],[918,0]],[[0,0],[0,0]],[[-162,270],[270,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
