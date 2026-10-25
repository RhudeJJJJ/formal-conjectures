/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode071
import Proofs.RadenkovicGutmanD38Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-77976,0],[-77976,-15732,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1311228,-1467180,0],[-1467180,-189012,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26815536,-11773692,0],[-11773692,-919676,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-243299484,-53423972,0],[-53423972,-2351364,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1302740244,-153222308,0],[-153222308,-3456328,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4620420000,-294441404,0],[-294441404,-3035288,0],[0,0]],[[0,0,0],[0,0],[0]],[[-11552249356,-392499492,0],[-392499492,-1604588],[0]],[[0,0,0],[0,0],[0]],[[-21158813592,-370584512,0],[-370584512,-498484],[0]],[[0,0,0],[0,0],[0]],[[-29112808748,-250440064,0],[-250440064,-83676],[0]],[[0,0,0],[0,0],[0]],[[-30595995868,-121253820,0],[-121253820,-5852],[0]],[[0,0,0],[0,0],[0]],[[-24816412240,-41638500,0],[-41638500,0],[0]],[[0,0],[0]],[[-15616116872,-9887068],[-9887068]],[[0,0],[0]],[[-7626602204,-1542116],[-1542116]],[[0,0],[0]],[[-2876912056,-142044],[-142044]],[[0,0],[0]],[[-828948796,-5852],[-5852]],[[0,0],[0]],[[-178860680,0],[0]],[[0]],[[-27948164]],[[0]],[[-2984368]],[[0]],[[-194712]],[[0]],[[-5852]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
