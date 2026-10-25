/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode043
import Proofs.RadenkovicGutmanD13Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,1521],[0,3042,-1716],[1521,-1716,484]],[[0,0,0],[0,0,0],[0,0]],[[0,53001,-2262],[53001,-34422,1276],[-2262,1276]],[[0,0,0],[0,0,0],[0,0]],[[376164,189675,-24119],[189675,-177466,14080],[-24119,14080]],[[0,0,0],[0,0,0],[0,0]],[[2508408,-339597,-12094],[-339597,-174030,17292],[-12094,17292]],[[0,0,0],[0,0,0],[0,0]],[[1789506,-2833352,112480],[-2833352,350228,7172],[112480,7172]],[[0,0,0],[0,0,0],[0,0]],[[-36238266,-5400365,259258],[-5400365,1001372,968],[259258,968]],[[0,0,0],[0,0],[0]],[[-178123170,-2127705,260045],[-2127705,1040302],[260045]],[[0,0,0],[0,0],[0]],[[-434227000,8195852,142198],[8195852,572970],[142198]],[[0,0,0],[0,0],[0]],[[-657853546,17193319,43861],[17193319,176646],[43861]],[[0,0,0],[0,0],[0]],[[-642458840,17284705,7172],[17284705,28798],[7172]],[[0,0,0],[0,0],[0]],[[-367015716,10802912,484],[10802912,1936],[484]],[[0,0],[0]],[[-39748410,4458305],[4458305]],[[0,0],[0]],[[136775482,1219701],[1219701]],[[0,0],[0]],[[144282886,213307],[213307]],[[0,0],[0]],[[82875918,21626],[21626]],[[0,0],[0]],[[31836324,968],[968]],[[0]],[[8535450]],[[0]],[[1586796]],[[0]],[[195780]],[[0]],[[14454]],[[0]],[[484]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
