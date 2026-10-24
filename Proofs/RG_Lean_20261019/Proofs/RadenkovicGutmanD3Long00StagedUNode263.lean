/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode214
import Proofs.RadenkovicGutmanD3Long00StagedUNode184
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e263 : NestedArithmetic.Expr 3 := .times e214 e184
noncomputable def p263 : NestedHorner.Poly 3 := [[[12],[0],[0]],[[0,0],[0,0],[0]],[[366,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5094,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[42798,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[241848,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[968592,18,0],[18,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2817300,393,0],[393,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5976438,3771,0],[3771,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[9065682,20835,0],[20835,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[9161052,72780,0],[72780,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4561662,165141,6],[165141,24,0],[6,0]],[[0,0,0],[0,0,0],[0,0]],[[-2298918,236331,81],[236331,342,0],[81,0]],[[0,0,0],[0,0,0],[0,0]],[[-6601380,180456,438],[180456,2004,0],[438,0]],[[0,0,0],[0,0,0],[0,0]],[[-6262416,-5265,1185],[-5265,6198,0],[1185,0]],[[0,0,0],[0,0,0],[0,0]],[[-3473496,-164151,1566],[-164151,10764,0],[1566,0]],[[0,0,0],[0,0,0],[0,0]],[[-1179198,-172866,546],[-172866,10176,6],[546,6]],[[0,0,0],[0,0,0],[0,0]],[[-226962,-88803,-990],[-88803,4284,42],[-990,42]],[[0,0,0],[0,0,0],[0,0]],[[-18954,-23409,-1251],[-23409,-234,96],[-1251,96]],[[0,0,0],[0,0,0],[0,0]],[[0,-2511,-540],[-2511,-756,78],[-540,78]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-81],[0,-162,18],[-81,18]]]
theorem step263 : p263=NestedArithmetic.mul p214 p184 := by decide +kernel
#print axioms step263
theorem h263 : NestedArithmetic.compile e263=p263 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e214) (NestedArithmetic.compile e184)=p263
  rw [h214,h184]
  exact step263.symm
#print axioms h263
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
