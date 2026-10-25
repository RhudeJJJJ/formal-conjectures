/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode100
import Proofs.RadenkovicGutmanD19Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,361]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-3249],[0,-6498,10602],[-3249,10602,38]],[[0,0,0],[0,0,0],[0,0]],[[-29241,-109269,38019],[-109269,203262,35796],[38019,35796]],[[0,0,0],[0,0,0],[0,0]],[[-1353294,251883,321917],[251883,1434538,39596],[321917,39596]],[[0,0,0],[0,0,0],[0,0]],[[-7375401,7506729,916066],[7506729,3843890,17024],[916066,17024]],[[0,0,0],[0,0,0],[0,0]],[[7542924,37355520,1345428],[37355520,5441220,2698],[1345428,2698]],[[0,0,0],[0,0,0],[0,0]],[[207482717,96358709,1145244],[96358709,4508396,76],[1145244,76]],[[0,0,0],[0,0],[0]],[[953215636,155319395,585219],[155319395,2256858],[585219]],[[0,0,0],[0,0],[0]],[[2486634310,168477256,177726],[168477256,674842],[177726]],[[0,0,0],[0,0],[0]],[[4369942202,127274597,30039],[127274597,112898],[30039]],[[0,0,0],[0,0],[0]],[[5531979960,67849931,2337],[67849931,8778],[2337]],[[0,0,0],[0,0],[0]],[[5217222464,25459734,38],[25459734,152],[38]],[[0,0],[0]],[[3731228930,6597275],[6597275]],[[0,0],[0]],[[2039552910,1131127],[1131127]],[[0,0],[0]],[[852246197,117629],[117629]],[[0,0],[0]],[[270249996,6080],[6080]],[[0,0],[0]],[[63985578,76],[76]],[[0]],[[10989030]],[[0]],[[1302279]],[[0]],[[97166]],[[0]],[[3743]],[[0]],[[38]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
