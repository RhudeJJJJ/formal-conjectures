/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e099
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-150],[0,-150,30]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-1800],[0,-6435,-140],[-1800,-140]],[[0,0,0],[0,0,0],[0,0]],[[-7695,-52785,-11190],[-52785,-38040,510],[-11190,510]],[[0,0,0],[0,0,0],[0,0]],[[-488565,-498420,-28280],[-498420,-89815,810],[-28280,810]],[[0,0,0],[0,0,0],[0,0]],[[-5443740,-2065275,-36810],[-2065275,-105660,360],[-36810,360]],[[0,0,0],[0,0,0],[0,0]],[[-29570055,-4946510,-25570],[-4946510,-59960,50],[-25570,50]],[[0,0,0],[0,0],[0]],[[-98470295,-7597925,-8230],[-7597925,-7230],[-8230]],[[0,0,0],[0,0],[0]],[[-222243640,-7846720,60],[-7846720,9625],[60]],[[0,0,0],[0,0],[0]],[[-358797500,-5544170,850],[-5544170,5400],[850]],[[0,0,0],[0,0],[0]],[[-427548205,-2661100,230],[-2661100,1145],[230]],[[0,0,0],[0,0],[0]],[[-382856200,-831895,20],[-831895,90],[20]],[[0,0],[0]],[[-259811490,-147780],[-147780]],[[0,0],[0]],[[-133625500,-5875],[-5875]],[[0,0],[0]],[[-51610425,3210],[3210]],[[0,0],[0]],[[-14635055,645],[645]],[[0,0],[0]],[[-2903520,40],[40]],[[0]],[[-357800]],[[0]],[[-15875]],[[0]],[[2405]],[[0]],[[415]],[[0]],[[20]]]
theorem step103 : p103=NestedHorner.scale (-1) p099 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e099 p099 p103 rfl h099 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
