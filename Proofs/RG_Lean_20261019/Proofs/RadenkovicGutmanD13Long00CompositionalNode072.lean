/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode051
import Proofs.RadenkovicGutmanD13Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,507],[0,507,-286]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-4563,7605],[-4563,22815,-4589],[7605,-4589,-44]],[[0,0,0],[0,0,0],[0,0]],[[-45279,135837,20397],[135837,14652,-18914],[20397,-18914]],[[0,0,0],[0,0,0],[0,0]],[[518373,812340,-52522],[812340,-442905,-22249],[-52522,-22249]],[[0,0,0],[0,0,0],[0,0]],[[5963220,138269,-299275],[138269,-1614320,-10165],[-299275,-10165]],[[0,0,0],[0,0,0],[0,0]],[[13048791,-9994700,-541734],[-9994700,-2594328,-1822],[-541734,-1822]],[[0,0,0],[0,0,0],[0,0]],[[-52766239,-36665627,-515041],[-36665627,-2322030,-88],[-515041,-88]],[[0,0,0],[0,0],[0]],[[-398380972,-68789010,-284294],[-68789010,-1234121],[-284294]],[[0,0,0],[0,0],[0]],[[-1209681388,-81448275,-92545],[-81448275,-391244],[-92545]],[[0,0,0],[0,0],[0]],[[-2296945137,-65270309,-17011],[-65270309,-70485],[-17011]],[[0,0,0],[0,0],[0]],[[-3049504762,-36388926,-1536],[-36388926,-6258],[-1536]],[[0,0,0],[0,0],[0]],[[-2971047444,-14187542,-44],[-14187542,-176],[-44]],[[0,0],[0]],[[-2176509868,-3817622],[-3817622]],[[0,0],[0]],[[-1212772815,-684020],[-684020]],[[0,0],[0]],[[-515327491,-75808],[-75808]],[[0,0],[0]],[[-166087008,-4436],[-4436]],[[0,0],[0]],[[-40027104,-88],[-88]],[[0]],[[-7027195]],[[0]],[[-859149]],[[0]],[[-67509]],[[0]],[[-2900]],[[0]],[[-44]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
