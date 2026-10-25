/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode043
import Proofs.RadenkovicGutmanD32Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3072],[0,3072,-1920]],[[0,0,0],[0,0,0],[0,0]],[[0,27648,27648],[27648,112896,-21248],[27648,-21248]],[[0,0,0],[0,0,0],[0,0]],[[673920,1126656,38016],[1126656,172032,-75776],[38016,-75776]],[[0,0,0],[0,0,0],[0,0]],[[15517440,6651648,-294912],[6651648,-1111808,-77312],[-294912,-77312]],[[0,0,0],[0,0,0],[0,0]],[[123341184,15214336,-1091072],[15214336,-4247040,-29696],[-1091072,-29696]],[[0,0,0],[0,0,0],[0,0]],[[522681600,8116224,-1652736],[8116224,-6497280,-3840],[-1652736,-3840]],[[0,0,0],[0,0],[0]],[[1373777536,-34979072,-1374464],[-34979072,-5433856],[-1374464]],[[0,0,0],[0,0],[0]],[[2376313344,-95776000,-671744],[-95776000,-2666240],[-671744]],[[0,0,0],[0,0],[0]],[[2698880768,-124965376,-192000],[-124965376,-764416],[-192000]],[[0,0,0],[0,0],[0]],[[1782028544,-102454272,-29696],[-102454272,-118528],[-29696]],[[0,0,0],[0,0],[0]],[[135858176,-56594688,-1920],[-56594688,-7680],[-1920]],[[0,0],[0]],[[-1111511040,-21431040],[-21431040]],[[0,0],[0]],[[-1376137216,-5496064],[-5496064]],[[0,0],[0]],[[-967321856,-913408],[-913408]],[[0,0],[0]],[[-465776000,-88832],[-88832]],[[0,0],[0]],[[-160872960,-3840],[-3840]],[[0]],[[-40049920]],[[0]],[[-7040256]],[[0]],[[-830848]],[[0]],[[-59136]],[[0]],[[-1920]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
