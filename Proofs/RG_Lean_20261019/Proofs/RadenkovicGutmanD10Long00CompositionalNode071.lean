/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode043
import Proofs.RadenkovicGutmanD10Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-300],[0,-300,160]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-2700,-4500],[-2700,-15120,2480],[-4500,2480,32]],[[0,0,0],[0,0,0],[0,0]],[[-68040,-187380,-13440],[-187380,-31824,10556],[-13440,10556]],[[0,0,0],[0,0,0],[0,0]],[[-2288088,-1388376,23212],[-1388376,151440,12676],[23212,12676]],[[0,0,0],[0,0,0],[0,0]],[[-21860496,-4349152,158644],[-4349152,692096,5968],[158644,5968]],[[0,0,0],[0,0,0],[0,0]],[[-107276976,-6550272,297804],[-6550272,1179408,1132],[297804,1132]],[[0,0,0],[0,0,0],[0,0]],[[-325089288,-2426128,289060],[-2426128,1087056,64],[289060,64]],[[0,0,0],[0,0],[0]],[[-659798888,8545984,162452],[8545984,591728],[162452]],[[0,0,0],[0,0],[0]],[[-928468960,17974660,53980],[17974660,193184],[53980]],[[0,0,0],[0,0],[0]],[[-904323576,18378992,10216],[18378992,36480],[10216]],[[0,0,0],[0,0],[0]],[[-571957984,11864224,972],[11864224,3552],[972]],[[0,0,0],[0,0],[0]],[[-165134816,5143380,32],[5143380,128],[32]],[[0,0],[0]],[[81934840,1512140],[1512140]],[[0,0],[0]],[[131573440,295020],[295020]],[[0,0],[0]],[[85381784,36020],[36020]],[[0,0],[0]],[[35633592,2420],[2420]],[[0,0],[0]],[[10362832,64],[64]],[[0]],[[2123720]],[[0]],[[299800]],[[0]],[[27496]],[[0]],[[1448]],[[0]],[[32]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
