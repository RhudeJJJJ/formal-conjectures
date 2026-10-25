/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode033
import Proofs.RadenkovicGutmanD44Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5808],[0,5808,-3696]],[[0,0,0],[0,0,0],[0,0]],[[0,-52272,52272],[-52272,191664,-41360],[52272,-41360]],[[0,0,0],[0,0,0],[0,0]],[[-484704,574992,66528],[574992,115104,-146432],[66528,-146432]],[[0,0,0],[0,0,0],[0,0]],[[223344,2695968,-586080],[2695968,-2857360,-149072],[-586080,-149072]],[[0,0,0],[0,0,0],[0,0]],[[18585072,-6521680,-2126960],[-6521680,-9394528,-57200],[-2126960,-57200]],[[0,0,0],[0,0,0],[0,0]],[[52499568,-63884832,-3203904],[-63884832,-13675200,-7392],[-3203904,-7392]],[[0,0,0],[0,0],[0]],[[-110627264,-185000464,-2657072],[-185000464,-11112288],[-2657072]],[[0,0,0],[0,0],[0]],[[-1043488864,-304627136,-1296416],[-304627136,-5342480],[-1296416]],[[0,0,0],[0,0],[0]],[[-3203607264,-327079280,-370128],[-327079280,-1507616],[-370128]],[[0,0,0],[0,0],[0]],[[-6002343952,-241319760,-57200],[-241319760,-230736],[-57200]],[[0,0,0],[0,0],[0]],[[-7818474752,-124759008,-3696],[-124759008,-14784],[-3696]],[[0,0],[0]],[[-7463119488,-45154560],[-45154560]],[[0,0],[0]],[[-5353645440,-11209088],[-11209088]],[[0,0],[0]],[[-2918218160,-1818080],[-1818080]],[[0,0],[0]],[[-1210448448,-173536],[-173536]],[[0,0],[0]],[[-379307808,-7392],[-7392]],[[0]],[[-88257312]],[[0]],[[-14772912]],[[0]],[[-1680800]],[[0]],[[-116336]],[[0]],[[-3696]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
