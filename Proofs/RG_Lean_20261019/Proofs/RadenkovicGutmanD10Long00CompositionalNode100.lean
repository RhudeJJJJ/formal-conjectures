/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode043
import Proofs.RadenkovicGutmanD10Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-900],[0,-1800,480],[-900,480]],[[0,0,0],[0,0,0],[0,0]],[[0,-36180,-3480],[-36180,240,2080],[-3480,2080]],[[0,0,0],[0,0,0],[0,0]],[[-340200,-312660,3740],[-312660,55480,2560],[3740,2560]],[[0,0,0],[0,0,0],[0,0]],[[-4228200,-1074780,37720],[-1074780,200080,1120],[37720,1120]],[[0,0,0],[0,0,0],[0,0]],[[-23406840,-1761560,76720],[-1761560,322400,160],[76720,160]],[[0,0,0],[0,0],[0]],[[-76341600,-851740,76760],[-851740,286000],[76760]],[[0,0,0],[0,0],[0]],[[-162905760,2005420,42940],[2005420,147960],[42940]],[[0,0,0],[0,0],[0]],[[-237556240,4625200,13640],[4625200,44400],[13640]],[[0,0,0],[0,0],[0]],[[-237291480,4841860,2300],[4841860,7160],[2300]],[[0,0,0],[0,0],[0]],[[-152638040,3126220,160],[3126220,480],[160]],[[0,0],[0]],[[-44508160,1329080],[1329080]],[[0,0],[0]],[[22074200,373900],[373900]],[[0,0],[0]],[[35268760,67140],[67140]],[[0,0],[0]],[[22547760,6980],[6980]],[[0,0],[0]],[[9163200,320],[320]],[[0]],[[2553600]],[[0]],[[489400]],[[0]],[[61960]],[[0]],[[4680]],[[0]],[[160]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
