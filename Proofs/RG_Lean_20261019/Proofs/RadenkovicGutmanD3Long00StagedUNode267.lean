/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode171
import Proofs.RadenkovicGutmanD3Long00StagedUNode215
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e267 : NestedArithmetic.Expr 3 := .times e171 e215
noncomputable def p267 : NestedHorner.Poly 3 := [[[6],[0],[0]],[[0,0],[0,0],[0]],[[144,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1368,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5070,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16380,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-298854,12,0],[12,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1798254,225,0],[225,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6745338,1725,0],[1725,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17761050,6435,0],[6435,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34286760,7410,0],[7410,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-49373844,-36639,6],[-36639,18,0],[6,0]],[[0,0,0],[0,0,0],[0,0]],[[-53217198,-198021,81],[-198021,258,0],[81,0]],[[0,0,0],[0,0,0],[0,0]],[[-42627576,-477072,438],[-477072,1518,0],[438,0]],[[0,0,0],[0,0,0],[0,0]],[[-24920430,-702159,1185],[-702159,4698,0],[1185,0]],[[0,0,0],[0,0,0],[0,0]],[[-10287990,-672687,1566],[-672687,8100,0],[1566,0]],[[0,0,0],[0,0,0],[0,0]],[[-2829654,-420276,546],[-420276,7428,6],[546,6]],[[0,0,0],[0,0,0],[0,0]],[[-463320,-164619,-990],[-164619,2694,42],[-990,42]],[[0,0,0],[0,0,0],[0,0]],[[-34020,-36531,-1251],[-36531,-702,96],[-1251,96]],[[0,0,0],[0,0,0],[0,0]],[[0,-3483,-540],[-3483,-810,78],[-540,78]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-81],[0,-162,18],[-81,18]]]
theorem step267 : p267=NestedArithmetic.mul p171 p215 := by decide +kernel
#print axioms step267
theorem h267 : NestedArithmetic.compile e267=p267 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e171) (NestedArithmetic.compile e215)=p267
  rw [h171,h215]
  exact step267.symm
#print axioms h267
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
