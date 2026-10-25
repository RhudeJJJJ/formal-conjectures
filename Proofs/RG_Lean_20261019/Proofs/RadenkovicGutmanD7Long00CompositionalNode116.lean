/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode115
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e116 : NestedArithmetic.Expr 3 := .scaled (-1) e115
noncomputable def p116 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-49]],[[0,0],[0,0,0],[0,0]],[[0,0,-441],[0,0,-882],[-441,-882]],[[0,0,0],[0,0,0],[0,0]],[[-3969,-7938,-7791],[-7938,-15876,-2352],[-7791,-2352]],[[0,0,0],[0,0,0],[0,0]],[[-140238,-161406,-34153],[-161406,-84672,-2156],[-34153,-2156]],[[0,0,0],[0,0,0],[0,0]],[[-1853523,-1008126,-70070],[-1008126,-190512,-784],[-70070,-784]],[[0,0,0],[0,0,0],[0,0]],[[-12121914,-3250464,-80556],[-3250464,-235200,-98],[-80556,-98]],[[0,0,0],[0,0],[0]],[[-47536909,-6441638,-55664],[-6441638,-173656],[-55664]],[[0,0,0],[0,0],[0]],[[-124296340,-8513750,-23569],[-8513750,-78400],[-23569]],[[0,0,0],[0,0],[0]],[[-230620558,-7830004,-5978],[-7830004,-21168],[-5978]],[[0,0,0],[0,0],[0]],[[-315588322,-5117168,-833],[-5117168,-3136],[-833]],[[0,0,0],[0,0],[0]],[[-326404288,-2390710,-49],[-2390710,-196],[-49]],[[0,0],[0]],[[-259029680,-792330],[-792330]],[[0,0],[0]],[[-159003040,-181790],[-181790]],[[0,0],[0]],[[-75655118,-27440],[-27440]],[[0,0],[0]],[[-27797749,-2450],[-2450]],[[0,0],[0]],[[-7804524,-98],[-98]],[[0]],[[-1641990]],[[0]],[[-250390]],[[0]],[[-26117]],[[0]],[[-1666]],[[0]],[[-49]]]
theorem step116 : p116=NestedHorner.scale (-1) p115 := by decide +kernel
#print axioms step116
theorem h116 : NestedArithmetic.compile e116=p116 := StagedExprCompile.compile_scaled (-1) e116 e115 p115 p116 rfl h115 step116
#print axioms h116
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
