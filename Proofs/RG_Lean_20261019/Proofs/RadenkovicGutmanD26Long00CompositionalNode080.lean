/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode035
import Proofs.RadenkovicGutmanD26Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2028],[0,-2028]],[[0,0,0],[0,0,0],[0,0]],[[0,-18252,-18252],[-18252,-73008,-8788],[-18252,-8788]],[[0,0,0],[0,0,0],[0,0]],[[-328536,-730080,-127764],[-730080,-511056,-10816],[-127764,-10816]],[[0,0,0],[0,0,0],[0,0]],[[-8103888,-6084000,-352872],[-6084000,-1411488,-4732],[-352872,-4732]],[[0,0,0],[0,0,0],[0,0]],[[-72423936,-24075064,-511732],[-24075064,-2046928,-676],[-511732,-676]],[[0,0,0],[0,0],[0]],[[-351728208,-56260776,-429936],[-56260776,-1719744],[-429936]],[[0,0,0],[0,0],[0]],[[-1087790808,-85532928,-215644],[-85532928,-862576],[-215644]],[[0,0,0],[0,0],[0]],[[-2324726144,-88914280,-63544],[-88914280,-254176],[-63544]],[[0,0,0],[0,0],[0]],[[-3600684256,-64812852,-10140],[-64812852,-40560],[-10140]],[[0,0,0],[0,0],[0]],[[-4162276664,-33419412,-676],[-33419412,-2704],[-676]],[[0,0],[0]],[[-3656101384,-12120004],[-12120004]],[[0,0],[0]],[[-2464705464,-3021720],[-3021720]],[[0,0],[0]],[[-1279532800,-492804],[-492804]],[[0,0],[0]],[[-510104192,-47320],[-47320]],[[0,0],[0]],[[-154648520,-2028],[-2028]],[[0]],[[-34987056]],[[0]],[[-5716256]],[[0]],[[-636792]],[[0]],[[-43264]],[[0]],[[-1352]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
