/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode071
import Proofs.RadenkovicGutmanD17Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-15606,0],[-15606,-3825,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-268515,-299727,0],[-299727,-43860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5528655,-2426886,0],[-2426886,-205445,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-50316498,-11044271,0],[-11044271,-510000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-269654085,-31671578,0],[-31671578,-733720,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-956007087,-60771821,0],[-60771821,-634610,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2387692024,-80849790,0],[-80849790,-331925],[0]],[[0,0,0],[0,0],[0]],[[-4367035344,-76176524,0],[-76176524,-102340],[0]],[[0,0,0],[0,0],[0]],[[-5999318411,-51376822,0],[-51376822,-17085],[0]],[[0,0,0],[0,0],[0]],[[-6294965632,-24828687,0],[-24828687,-1190],[0]],[[0,0,0],[0,0],[0]],[[-5097943918,-8511798,0],[-8511798,0],[0]],[[0,0],[0]],[[-3203225612,-2018053],[-2018053]],[[0,0],[0]],[[-1562220083,-314330],[-314330]],[[0,0],[0]],[[-588538759,-28917],[-28917]],[[0,0],[0]],[[-169376848,-1190],[-1190]],[[0,0],[0]],[[-36505460,0],[0]],[[0]],[[-5698349]],[[0]],[[-607903]],[[0]],[[-39627]],[[0]],[[-1190]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
