/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode071
import Proofs.RadenkovicGutmanD32Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-55296,0],[-55296,-11520,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-933120,-1043712,0],[-1043712,-137280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19103040,-8387136,0],[-8387136,-663680,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-173406528,-38074496,0],[-38074496,-1688640,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-928627200,-109197248,0],[-109197248,-2473600,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3293355072,-209791616,0],[-209791616,-2167040,0],[0,0]],[[0,0,0],[0,0],[0]],[[-8232858304,-279572160,0],[-279572160,-1143680],[0]],[[0,0,0],[0,0],[0]],[[-15075763584,-263876864,0],[-263876864,-354880],[0]],[[0,0,0],[0,0],[0]],[[-20737988096,-178271872,0],[-178271872,-59520],[0]],[[0,0,0],[0,0],[0]],[[-21789134272,-86287872,0],[-86287872,-4160],[0]],[[0,0,0],[0,0],[0]],[[-17668916608,-29623488,0],[-29623488,0],[0]],[[0,0],[0]],[[-11115896192,-7032448],[-7032448]],[[0,0],[0]],[[-5427615488,-1096640],[-1096640]],[[0,0],[0]],[[-2046998464,-100992],[-100992]],[[0,0],[0]],[[-589709248,-4160],[-4160]],[[0,0],[0]],[[-127218560,0],[0]],[[0]],[[-19875584]],[[0]],[[-2122048]],[[0]],[[-138432]],[[0]],[[-4160]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
