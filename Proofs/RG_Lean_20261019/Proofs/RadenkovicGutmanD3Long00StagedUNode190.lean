/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode189
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e190 : NestedArithmetic.Expr 3 := .times e189 e120
noncomputable def p190 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[33,0],[0,0]],[[0,0],[0,0]],[[233,0],[0,0]],[[0,0],[0,0]],[[920,0],[0,0]],[[0,0],[0,0]],[[2229,0],[0,0]],[[0,0],[0,0]],[[3420,2],[2,0]],[[0,0],[0,0]],[[3296,19],[19,0]],[[0,0],[0,0]],[[1876,68],[68,0]],[[0,0],[0,0]],[[507,114],[114,0]],[[0,0],[0,0]],[[-9,90],[90,0]],[[0,0],[0,0]],[[-27,27],[27,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step190 : p190=NestedArithmetic.mul p189 p120 := by decide +kernel
#print axioms step190
theorem h190 : NestedArithmetic.compile e190=p190 := StagedExprCompile.compile_times e190 e189 e120 p189 p120 p190 rfl h189 h120 step190
#print axioms h190
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
