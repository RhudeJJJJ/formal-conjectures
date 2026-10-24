/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode051
import Proofs.RadenkovicGutmanD5Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,75],[0,75,-30]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-675,1125],[-675,3375,-365],[1125,-365,-12]],[[0,0,0],[0,0,0],[0,0]],[[-7695,20925,4845],[20925,9324,-1906],[4845,-1906]],[[0,0,0],[0,0,0],[0,0]],[[73413,169956,2918],[169956,-24105,-2521],[2918,-2521]],[[0,0,0],[0,0,0],[0,0]],[[1169316,417197,-18619],[417197,-140736,-1333],[-18619,-1333]],[[0,0,0],[0,0,0],[0,0]],[[5140551,-8668,-47414],[-8668,-260728,-302],[-47414,-302]],[[0,0,0],[0,0,0],[0,0]],[[8539873,-2212907,-52305],[-2212907,-255566,-24],[-52305,-24]],[[0,0,0],[0,0],[0]],[[-8300252,-5617954,-32182],[-5617954,-147353],[-32182]],[[0,0,0],[0,0],[0]],[[-72479820,-7646595,-11665],[-7646595,-51164],[-11665]],[[0,0,0],[0,0],[0]],[[-179039329,-6708197,-2451],[-6708197,-10405],[-2451]],[[0,0,0],[0,0],[0]],[[-271216426,-4018574,-272],[-4018574,-1122],[-272]],[[0,0,0],[0,0],[0]],[[-287584404,-1674390,-12],[-1674390,-48],[-12]],[[0,0],[0]],[[-224367340,-483190],[-483190]],[[0,0],[0]],[[-131719135,-94100],[-94100]],[[0,0],[0]],[[-58688099,-11680],[-11680]],[[0,0],[0]],[[-19822032,-820],[-820]],[[0,0],[0]],[[-5022912,-24],[-24]],[[0]],[[-934795]],[[0]],[[-123085]],[[0]],[[-10741]],[[0]],[[-548]],[[0]],[[-12]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
