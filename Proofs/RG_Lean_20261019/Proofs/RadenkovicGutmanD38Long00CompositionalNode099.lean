/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode096
import Proofs.RadenkovicGutmanD38Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,8664],[0,8664,-2736]],[[0,0,0],[0,0,0],[0,0]],[[0,0,103968],[0,353628,-11476],[103968,-11476]],[[0,0,0],[0,0,0],[0,0]],[[363204,2872800,551532],[2872800,1665996,-84132],[551532,-84132]],[[0,0,0],[0,0,0],[0,0]],[[25145208,24983100,1105268],[24983100,2582404,-98952],[1105268,-98952]],[[0,0,0],[0,0,0],[0,0]],[[271539108,94596516,889200],[94596516,369132,-40356],[889200,-40356]],[[0,0,0],[0,0,0],[0,0]],[[1416613020,203532788,-106628],[203532788,-3532024,-5396],[-106628,-5396]],[[0,0,0],[0,0],[0]],[[4510340384,271381940,-732488],[271381940,-4692696],[-732488]],[[0,0,0],[0,0],[0]],[[9679411756,226213924,-564756],[226213924,-2838220],[-564756]],[[0,0,0],[0,0],[0]],[[14733760520,106578752,-204592],[106578752,-921348],[-204592]],[[0,0,0],[0,0],[0]],[[16331441716,11092732,-36860],[11092732,-155420],[-36860]],[[0,0,0],[0,0],[0]],[[13303142524,-19884944,-2660],[-19884944,-10716],[-2660]],[[0,0],[0]],[[7895265624,-14386344],[-14386344]],[[0,0],[0]],[[3283643536,-5007716],[-5007716]],[[0,0],[0]],[[839757972,-1005024],[-1005024]],[[0,0],[0]],[[47644856,-111492],[-111492]],[[0,0],[0]],[[-59169876,-5320],[-5320]],[[0]],[[-27652600]],[[0]],[[-6536836]],[[0]],[[-924920]],[[0]],[[-74632]],[[0]],[[-2660]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
