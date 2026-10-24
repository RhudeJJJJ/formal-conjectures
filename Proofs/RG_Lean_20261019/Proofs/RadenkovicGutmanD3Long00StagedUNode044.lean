/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode043
import Proofs.RadenkovicGutmanD3Long00StagedUNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e044 : NestedArithmetic.Expr 3 := .times e043 e031
noncomputable def p044 : NestedHorner.Poly 3 := [[[0],[0,3]],[[0,0],[0,0]],[[-27,27],[27,2]],[[0,0],[0]],[[-9,90],[90]],[[0,0],[0]],[[507,114],[114]],[[0,0],[0]],[[1876,68],[68]],[[0,0],[0]],[[3296,19],[19]],[[0,0],[0]],[[3420,2],[2]],[[0]],[[2229]],[[0]],[[920]],[[0]],[[233]],[[0]],[[33]],[[0]],[[2]]]
theorem step044 : p044=NestedArithmetic.mul p043 p031 := by decide +kernel
#print axioms step044
theorem h044 : NestedArithmetic.compile e044=p044 := StagedExprCompile.compile_times e044 e043 e031 p043 p031 p044 rfl h043 h031 step044
#print axioms h044
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
