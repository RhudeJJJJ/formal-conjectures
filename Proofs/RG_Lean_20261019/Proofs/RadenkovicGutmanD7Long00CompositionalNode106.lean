/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode095
import Proofs.RadenkovicGutmanD7Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-504,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4536,-4536,0],[-4536,-4368,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-119448,-51408,0],[-51408,-14840,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1179360,-249480,0],[-249480,-25648,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6355608,-687120,0],[-687120,-24864,0],[0,0]],[[0,0,0],[0,0],[0]],[[-21720104,-1201256,0],[-1201256,-14000],[0]],[[0,0,0],[0,0],[0]],[[-50930768,-1410080,0],[-1410080,-4536],[0]],[[0,0,0],[0,0],[0]],[[-85875104,-1143856,0],[-1143856,-784],[0]],[[0,0,0],[0,0],[0]],[[-107227848,-648480,0],[-648480,-56],[0]],[[0,0,0],[0,0],[0]],[[-100998800,-255976,0],[-255976,0],[0]],[[0,0],[0]],[[-72525264,-68880],[-68880]],[[0,0],[0]],[[-39866624,-12040],[-12040]],[[0,0],[0]],[[-16740136,-1232],[-1232]],[[0,0],[0]],[[-5320840,-56],[-56]],[[0,0],[0]],[[-1256976,0],[0]],[[0]],[[-213696]],[[0]],[[-24696]],[[0]],[[-1736]],[[0]],[[-56]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
