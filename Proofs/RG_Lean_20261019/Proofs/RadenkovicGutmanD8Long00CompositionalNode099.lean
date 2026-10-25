/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode096
import Proofs.RadenkovicGutmanD8Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,384],[0,384,-96]],[[0,0,0],[0,0,0],[0,0]],[[0,0,4608],[0,16128,-16],[4608,-16]],[[0,0,0],[0,0,0],[0,0]],[[18144,131760,26832],[131760,87216,-2352],[26832,-2352]],[[0,0,0],[0,0,0],[0,0]],[[1191888,1203120,62288],[1203120,180064,-3072],[62288,-3072]],[[0,0,0],[0,0,0],[0,0]],[[13115088,4814496,70560],[4814496,160752,-1296],[70560,-1296]],[[0,0,0],[0,0,0],[0,0]],[[70123200,11090288,35152],[11090288,19616,-176],[35152,-176]],[[0,0,0],[0,0],[0]],[[229551824,16245440,-2048],[16245440,-79296],[-2048]],[[0,0,0],[0,0],[0]],[[508515376,15742864,-10896],[15742864,-68320],[-10896]],[[0,0,0],[0,0],[0]],[[803873120,10104032,-5152],[10104032,-25488],[-5152]],[[0,0,0],[0,0],[0]],[[934451776,4082992,-1040],[4082992,-4640],[-1040]],[[0,0,0],[0,0],[0]],[[811487344,829456,-80],[829456,-336],[-80]],[[0,0],[0]],[[529013184,-60384],[-60384]],[[0,0],[0]],[[257209216,-87296],[-87296]],[[0,0],[0]],[[91141632,-23904],[-23904]],[[0,0],[0]],[[22199216,-3072],[-3072]],[[0,0],[0]],[[3090864,-160],[-160]],[[0]],[[-8800]],[[0]],[[-102016]],[[0]],[[-21200]],[[0]],[[-2032]],[[0]],[[-80]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
