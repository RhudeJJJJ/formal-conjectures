/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode042
import Proofs.RadenkovicGutmanD3Long00StagedUNode060
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e065 : NestedArithmetic.Expr 3 := .times e042 e060
noncomputable def p065 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,81],[0,162,-36],[81,-36,4]],[[0,0,0],[0,0,0],[0,0]],[[0,3321,378],[3321,18,-84],[378,-84]],[[0,0,0],[0,0,0],[0,0]],[[29484,28755,441],[28755,-3786,0],[441,0]],[[0,0,0],[0,0,0],[0,0]],[[351648,101763,-414],[101763,-12550,92],[-414,92]],[[0,0,0],[0,0,0],[0,0]],[[1832706,181968,-1200],[181968,-17372,52],[-1200,52]],[[0,0,0],[0,0,0],[0,0]],[[5431854,144195,-582],[144195,-11268,8],[-582,8]],[[0,0,0],[0,0],[0]],[[9837430,-45985,445],[-45985,-2178],[445]],[[0,0,0],[0,0],[0]],[[10313080,-221428,598],[-221428,1330],[598]],[[0,0,0],[0,0],[0]],[[3281014,-228281,261],[-228281,886],[261]],[[0,0,0],[0,0],[0]],[[-7761920,-120175,52],[-120175,198],[52]],[[0,0,0],[0,0],[0]],[[-14803796,-29528,4],[-29528,16],[4]],[[0,0],[0]],[[-14052010,1905],[1905]],[[0,0],[0]],[[-8717318,3581],[3581]],[[0,0],[0]],[[-3727714,1067],[1067]],[[0,0],[0]],[[-1084922,146],[146]],[[0,0],[0]],[[-195756,8],[8]],[[0]],[[-13350]],[[0]],[[2836]],[[0]],[[860]],[[0]],[[94]],[[0]],[[4]]]
theorem step065 : p065=NestedArithmetic.mul p042 p060 := by decide +kernel
#print axioms step065
theorem h065 : NestedArithmetic.compile e065=p065 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e042) (NestedArithmetic.compile e060)=p065
  rw [h042,h060]
  exact step065.symm
#print axioms h065
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
