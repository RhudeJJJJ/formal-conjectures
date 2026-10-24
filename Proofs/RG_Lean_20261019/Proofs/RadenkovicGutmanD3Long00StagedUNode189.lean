/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode188
import Proofs.RadenkovicGutmanD3Long00StagedUNode156
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e189 : NestedArithmetic.Expr 3 := .times e188 e156
noncomputable def p189 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[33,0],[0,0]],[[0,0],[0,0]],[[233,0],[0,0]],[[0,0],[0,0]],[[920,0],[0,0]],[[0,0],[0,0]],[[2229,0],[0,0]],[[0,0],[0,0]],[[3420,2],[2,0]],[[0,0],[0,0]],[[3296,19],[19,0]],[[0,0],[0,0]],[[1876,68],[68,0]],[[0,0],[0,0]],[[507,114],[114,0]],[[0,0],[0,0]],[[-9,90],[90,0]],[[0,0],[0,0]],[[-27,27],[27,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step189 : p189=NestedArithmetic.mul p188 p156 := by decide +kernel
#print axioms step189
theorem h189 : NestedArithmetic.compile e189=p189 := StagedExprCompile.compile_times e189 e188 e156 p188 p156 p189 rfl h188 h156 step189
#print axioms h189
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
