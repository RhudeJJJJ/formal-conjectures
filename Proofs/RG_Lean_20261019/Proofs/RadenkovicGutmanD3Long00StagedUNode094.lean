/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode042
import Proofs.RadenkovicGutmanD3Long00StagedUNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e042 e052
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,27],[0,27,-6]],[[0,0,0],[0,0,0],[0,0]],[[0,243,243],[243,1188,9],[243,9]],[[0,0,0],[0,0,0],[0,0]],[[6804,11664,1215],[11664,6732,-144],[1215,-144]],[[0,0,0],[0,0,0],[0,0]],[[167508,94284,2106],[94284,14784,-201],[2106,-201]],[[0,0,0],[0,0,0],[0,0]],[[1495422,357462,981],[357462,14916,-87],[981,-87]],[[0,0,0],[0,0,0],[0,0]],[[7284204,792738,-1476],[792738,4752,-12],[-1476,-12]],[[0,0,0],[0,0],[0]],[[22624500,1122216,-2445],[1122216,-3780],[-2445]],[[0,0,0],[0,0],[0]],[[48471744,1047750,-1554],[1047750,-4272],[-1554]],[[0,0,0],[0,0],[0]],[[74904276,639453,-513],[639453,-1716],[-513]],[[0,0,0],[0,0],[0]],[[85703646,235221,-87],[235221,-324],[-87]],[[0,0,0],[0,0],[0]],[[73635834,33177,-6],[33177,-24],[-6]],[[0,0],[0]],[[47719590,-12510],[-12510]],[[0,0],[0]],[[23193984,-7959],[-7959]],[[0,0],[0]],[[8288952,-1938],[-1938]],[[0,0],[0]],[[2075664,-237],[-237]],[[0,0],[0]],[[318204,-12],[-12]],[[0]],[[12420]],[[0]],[[-6306]],[[0]],[[-1506]],[[0]],[[-150]],[[0]],[[-6]]]
theorem step094 : p094=NestedArithmetic.mul p042 p052 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e042 e052 p042 p052 p094 rfl h042 h052 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
