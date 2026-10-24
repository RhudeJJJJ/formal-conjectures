/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode034
import Proofs.RadenkovicGutmanD3Long00StagedUNode060
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .times e034 e060
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-81],[0,-162,18],[-81,18]],[[0,0,0],[0,0,0],[0,0]],[[0,-2511,-540],[-2511,-756,78],[-540,78]],[[0,0,0],[0,0,0],[0,0]],[[-18954,-23409,-1251],[-23409,-234,96],[-1251,96]],[[0,0,0],[0,0,0],[0,0]],[[-226962,-88803,-990],[-88803,4284,42],[-990,42]],[[0,0,0],[0,0,0],[0,0]],[[-1179198,-172866,546],[-172866,10176,6],[546,6]],[[0,0,0],[0,0],[0]],[[-3473496,-164151,1566],[-164151,10764],[1566]],[[0,0,0],[0,0],[0]],[[-6262416,-5265,1185],[-5265,6198],[1185]],[[0,0,0],[0,0],[0]],[[-6601380,180456,438],[180456,2004],[438]],[[0,0,0],[0,0],[0]],[[-2298918,236331,81],[236331,342],[81]],[[0,0,0],[0,0],[0]],[[4561662,165141,6],[165141,24],[6]],[[0,0],[0]],[[9161052,72780],[72780]],[[0,0],[0]],[[9065682,20835],[20835]],[[0,0],[0]],[[5976438,3771],[3771]],[[0,0],[0]],[[2817300,393],[393]],[[0,0],[0]],[[968592,18],[18]],[[0]],[[241848]],[[0]],[[42798]],[[0]],[[5094]],[[0]],[[366]],[[0]],[[12]]]
theorem step092 : p092=NestedArithmetic.mul p034 p060 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e034) (NestedArithmetic.compile e060)=p092
  rw [h034,h060]
  exact step092.symm
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
