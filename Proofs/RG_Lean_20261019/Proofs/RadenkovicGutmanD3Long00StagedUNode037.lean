/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode036
import Proofs.RadenkovicGutmanD3Long00StagedUNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e037 : NestedArithmetic.Expr 3 := .times e036 e031
noncomputable def p037 : NestedHorner.Poly 3 := [[[0],[0,-1]],[[0,0],[0]],[[9,-9],[-9]],[[0,0],[0]],[[-3,-24],[-24]],[[0,0],[0]],[[-167,-22],[-22]],[[0,0],[0]],[[-514,-8],[-8]],[[0,0],[0]],[[-756,-1],[-1]],[[0]],[[-636]],[[0]],[[-319]],[[0]],[[-94]],[[0]],[[-15]],[[0]],[[-1]]]
theorem step037 : p037=NestedArithmetic.mul p036 p031 := by decide +kernel
#print axioms step037
theorem h037 : NestedArithmetic.compile e037=p037 := StagedExprCompile.compile_times e037 e036 e031 p036 p031 p037 rfl h036 h031 step037
#print axioms h037
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
