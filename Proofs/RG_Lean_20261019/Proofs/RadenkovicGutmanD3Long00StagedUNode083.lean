/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode071
import Proofs.RadenkovicGutmanD3Long00StagedUNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e071 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-216,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1944,-3888,0],[-3888,-2250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-83754,-50706,0],[-50706,-9636,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1042146,-286092,0],[-286092,-22122,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6656544,-922950,0],[-922950,-29892,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26342394,-1899996,0],[-1899996,-24648,0],[0,0]],[[0,0,0],[0,0],[0]],[[-70779270,-2641638,0],[-2641638,-12444],[0]],[[0,0,0],[0,0],[0]],[[-136140348,-2560680,0],[-2560680,-3738],[0]],[[0,0,0],[0,0],[0]],[[-193795872,-1759404,0],[-1759404,-612],[0]],[[0,0,0],[0,0],[0]],[[-208599702,-860664,0],[-860664,-42],[0]],[[0,0,0],[0,0],[0]],[[-172084380,-297390,0],[-297390,0],[0]],[[0,0],[0]],[[-109591980,-70860],[-70860]],[[0,0],[0]],[[-53975016,-11070],[-11070]],[[0,0],[0]],[[-20479398,-1020],[-1020]],[[0,0],[0]],[[-5924046,-42],[-42]],[[0,0],[0]],[[-1281420,0],[0]],[[0]],[[-200520]],[[0]],[[-21426]],[[0]],[[-1398]],[[0]],[[-42]],[[0]],[[0]]]
theorem step083 : p083=NestedHorner.add p071 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e071 e082 p071 p082 p083 rfl h071 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
