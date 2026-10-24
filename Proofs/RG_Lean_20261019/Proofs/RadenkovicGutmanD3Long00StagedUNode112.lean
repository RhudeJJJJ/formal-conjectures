/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode034
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .pow e034 2
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,81],[0,162],[81]],[[0,0,0],[0,0],[0]],[[0,2916,702],[2916,1404],[702]],[[0,0,0],[0,0],[0]],[[26244,33048,2385],[33048,4770],[2385]],[[0,0,0],[0,0],[0]],[[367416,160380,4122],[160380,8244],[4122]],[[0,0,0],[0,0],[0]],[[2300724,441720,3996],[441720,7992],[3996]],[[0,0,0],[0,0],[0]],[[8574984,772236,2250],[772236,4500],[2250]],[[0,0,0],[0,0],[0]],[[21347064,906480,729],[906480,1458],[729]],[[0,0,0],[0,0],[0]],[[37725912,735336,126],[735336,252],[126]],[[0,0,0],[0,0],[0]],[[49056876,416880,9],[416880,18],[9]],[[0,0],[0]],[[47962152,164556],[164556]],[[0,0],[0]],[[35687592,44280],[44280]],[[0,0],[0]],[[20308392,7740],[7740]],[[0,0],[0]],[[8822988,792],[792]],[[0,0],[0]],[[2900376,36],[36]],[[0]],[[708408]],[[0]],[[124488]],[[0]],[[14868]],[[0]],[[1080]],[[0]],[[36]]]
theorem step112 : p112=NestedArithmetic.power p034 2 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := by
  change NestedArithmetic.power (NestedArithmetic.compile e034) 2=p112
  rw [h034]
  exact step112.symm
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
