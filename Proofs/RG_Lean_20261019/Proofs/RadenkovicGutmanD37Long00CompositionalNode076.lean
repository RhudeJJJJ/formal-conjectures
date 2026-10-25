/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode035
import Proofs.RadenkovicGutmanD37Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-12321],[0,-24642],[-12321]],[[0,0,0],[0,0],[0]],[[0,-406593,-106782],[-406593,-213564],[-106782]],[[0,0,0],[0,0],[0]],[[-3326670,-4546449,-362785],[-4546449,-725570],[-362785]],[[0,0,0],[0,0],[0]],[[-45464490,-21721923,-627002],[-21721923,-1254004],[-627002]],[[0,0,0],[0,0],[0]],[[-277148574,-58798550,-607836],[-58798550,-1215672],[-607836]],[[0,0,0],[0,0],[0]],[[-1003225104,-100926787,-342250],[-100926787,-684500],[-342250]],[[0,0,0],[0,0],[0]],[[-2421207924,-116278753,-110889],[-116278753,-221778],[-110889]],[[0,0,0],[0,0],[0]],[[-4142752804,-92593684,-19166],[-92593684,-38332],[-19166]],[[0,0,0],[0,0],[0]],[[-5210969814,-51555171,-1369],[-51555171,-2738],[-1369]],[[0,0],[0]],[[-4925604502,-19999721],[-19999721]],[[0,0],[0]],[[-3542599632,-5292554],[-5292554]],[[0,0],[0]],[[-1948604482,-910385],[-910385]],[[0,0],[0]],[[-818412842,-91723],[-91723]],[[0,0],[0]],[[-260148332,-4107],[-4107]],[[0]],[[-61457148]],[[0]],[[-10448208]],[[0]],[[-1207458]],[[0]],[[-84878]],[[0]],[[-2738]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
