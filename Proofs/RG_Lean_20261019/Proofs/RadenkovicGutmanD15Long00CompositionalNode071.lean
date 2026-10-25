/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode043
import Proofs.RadenkovicGutmanD15Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-675],[0,-675,390]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-6075,-10125],[-6075,-33480,6345],[-10125,6345,52]],[[0,0,0],[0,0,0],[0,0]],[[-150660,-414720,-25785],[-414720,-49464,25806],[-25785,25806]],[[0,0,0],[0,0,0],[0,0]],[[-5027508,-2947266,77742],[-2947266,455580,30081],[77742,30081]],[[0,0,0],[0,0,0],[0,0]],[[-47209446,-8559252,416619],[-8559252,1812776,13553],[416619,13553]],[[0,0,0],[0,0,0],[0,0]],[[-226672956,-10488462,743394],[-10488462,2955328,2362],[743394,2362]],[[0,0,0],[0,0,0],[0,0]],[[-668271288,3400302,700665],[3400302,2644236,104],[700665,104]],[[0,0,0],[0,0],[0]],[[-1307163668,31301324,383722],[31301324,1399068],[383722]],[[0,0,0],[0,0],[0]],[[-1740671300,51626615,123745],[51626615,441424],[123745]],[[0,0,0],[0,0],[0]],[[-1536157346,48480547,22431],[48480547,79360],[22431]],[[0,0,0],[0,0],[0]],[[-754086614,29777339,1972],[29777339,7092],[1972]],[[0,0,0],[0,0],[0]],[[59442574,12426580,52],[12426580,208],[52]],[[0,0],[0]],[[449426840,3525465],[3525465]],[[0,0],[0]],[[419420500,661070],[661070]],[[0,0],[0]],[[234842804,76595],[76595]],[[0,0],[0]],[[90765592,4730],[4730]],[[0,0],[0]],[[25017852,104],[104]],[[0]],[[4895670]],[[0]],[[658990]],[[0]],[[57026]],[[0]],[[2758]],[[0]],[[52]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
