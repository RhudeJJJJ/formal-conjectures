/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode043
import Proofs.RadenkovicGutmanD20Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-3600],[0,-7200,2160],[-3600,2160]],[[0,0,0],[0,0,0],[0,0]],[[0,-142560,-11760],[-142560,8880,9360],[-11760,9360]],[[0,0,0],[0,0,0],[0,0]],[[-1328400,-1170720,30080],[-1170720,276160,11520],[30080,11520]],[[0,0,0],[0,0,0],[0,0]],[[-16124400,-3652560,192640],[-3652560,946160,5040],[192640,5040]],[[0,0,0],[0,0,0],[0,0]],[[-86741280,-4553520,367440],[-4553520,1495200,720],[367440,720]],[[0,0,0],[0,0],[0]],[[-272821200,2269520,357920],[2269520,1312000],[357920]],[[0,0,0],[0,0],[0]],[[-553919120,16427840,197280],[16427840,673920],[197280]],[[0,0,0],[0,0],[0]],[[-747867680,27008800,62080],[27008800,201200],[62080]],[[0,0,0],[0,0],[0]],[[-645728160,25403520,10400],[25403520,32320],[10400]],[[0,0,0],[0,0],[0]],[[-271157680,15533440,720],[15533440,2160],[720]],[[0,0],[0]],[[110358080,6384960],[6384960]],[[0,0],[0]],[[276370400,1754800],[1754800]],[[0,0],[0]],[[235546720,309680],[309680]],[[0,0],[0]],[[126643920,31760],[31760]],[[0,0],[0]],[[47353200,1440],[1440]],[[0]],[[12559200]],[[0]],[[2328800]],[[0]],[[287920]],[[0]],[[21360]],[[0]],[[720]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
