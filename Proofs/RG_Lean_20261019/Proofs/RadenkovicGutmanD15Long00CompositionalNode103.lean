/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e099
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1350],[0,-1350,390]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-16200],[0,-55755,1080],[-16200,1080]],[[0,0,0],[0,0,0],[0,0]],[[-59535,-454005,-89370],[-454005,-278820,11130],[-89370,11130]],[[0,0,0],[0,0,0],[0,0]],[[-4029345,-4030560,-191340],[-4030560,-496695,13530],[-191340,13530]],[[0,0,0],[0,0,0],[0,0]],[[-43863120,-15633675,-183330],[-15633675,-265080,5580],[-183330,5580]],[[0,0,0],[0,0,0],[0,0]],[[-231279615,-34688730,-40710],[-34688730,297120,750],[-40710,750]],[[0,0,0],[0,0],[0]],[[-745406835,-48348525,70410],[-48348525,546210],[70410]],[[0,0,0],[0,0],[0]],[[-1622515620,-43465860,67680],[-43465860,359625],[67680]],[[0,0,0],[0,0],[0]],[[-2512624500,-24341010,26250],[-24341010,121500],[26250]],[[0,0,0],[0,0],[0]],[[-2847486165,-6891000,4890],[-6891000,20985],[4890]],[[0,0,0],[0,0],[0]],[[-2391802500,639165,360],[639165,1470],[360]],[[0,0],[0]],[[-1487651970,1411860],[1411860]],[[0,0],[0]],[[-672179100,586725],[586725]],[[0,0],[0]],[[-208362225,126930],[126930]],[[0,0],[0]],[[-36299715,14685],[14685]],[[0,0],[0]],[[1006740,720],[720]],[[0]],[[2559600]],[[0]],[[748725]],[[0]],[[115665]],[[0]],[[9795]],[[0]],[[360]]]
theorem step103 : p103=NestedHorner.scale (-1) p099 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e099 p099 p103 rfl h099 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
