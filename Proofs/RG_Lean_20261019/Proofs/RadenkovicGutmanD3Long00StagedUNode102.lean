/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode090
import Proofs.RadenkovicGutmanD3Long00StagedUNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e090 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1944,-1944,0],[-1944,-1818,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-50706,-21546,0],[-21546,-5892,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-492642,-101412,0],[-101412,-9402,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2597472,-267750,0],[-267750,-7908,0],[0,0]],[[0,0,0],[0,0],[0]],[[-8627658,-441204,0],[-441204,-3336],[0]],[[0,0,0],[0,0],[0]],[[-19500318,-475614,0],[-475614,-444],[0]],[[0,0,0],[0,0],[0]],[[-31346748,-339144,0],[-339144,150],[0]],[[0,0,0],[0,0],[0]],[[-36753888,-155364,0],[-155364,60],[0]],[[0,0,0],[0,0],[0]],[[-31796502,-40224,0],[-40224,6],[0]],[[0,0],[0]],[[-20260956,-2094],[-2094]],[[0,0],[0]],[[-9315132,2220],[2220]],[[0,0],[0]],[[-2902920,762],[762]],[[0,0],[0]],[[-486774,108],[108]],[[0,0],[0]],[[31386,6],[6]],[[0]],[[43092]],[[0]],[[12312]],[[0]],[[1902]],[[0]],[[162]],[[0]],[[6]]]
theorem step102 : p102=NestedHorner.add p090 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e090 e101 p090 p101 p102 rfl h090 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
