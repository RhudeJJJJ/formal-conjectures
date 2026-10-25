/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode051
import Proofs.RadenkovicGutmanD36Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3888],[0,-3888]],[[0,0,0],[0,0,0],[0,0]],[[0,34992,-58320],[34992,-174960,-17064],[-58320,-17064]],[[0,0,0],[0,0,0],[0,0]],[[524880,-1156680,-449064],[-1156680,-1290168,-21672],[-449064,-21672]],[[0,0,0],[0,0,0],[0,0]],[[-3003480,-14092056,-1377000],[-14092056,-3785184,-10224],[-1377000,-10224]],[[0,0,0],[0,0,0],[0,0]],[[-88609464,-66202272,-2205792],[-66202272,-5836248,-1800],[-2205792,-1800]],[[0,0,0],[0,0,0],[0,0]],[[-616555152,-174214872,-2029608],[-174214872,-5208336,-72],[-2029608,-72]],[[0,0,0],[0,0],[0]],[[-2335731336,-291469104,-1107216],[-291469104,-2776896],[-1107216]],[[0,0,0],[0,0],[0]],[[-5749330680,-329087592,-354744],[-329087592,-876096],[-354744]],[[0,0,0],[0,0],[0]],[[-9937854864,-258304896,-62496],[-258304896,-153432],[-62496]],[[0,0,0],[0,0],[0]],[[-12581318736,-142581672,-4968],[-142581672,-12384],[-4968]],[[0,0,0],[0,0],[0]],[[-11954182968,-55172232,-72],[-55172232,-216],[-72]],[[0,0],[0]],[[-8641690848,-14676048],[-14676048]],[[0,0],[0]],[[-4780677888,-2568672],[-2568672]],[[0,0],[0]],[[-2021923728,-270288],[-270288]],[[0,0],[0]],[[-648497016,-13824],[-13824]],[[0,0],[0]],[[-155080440,-144],[-144]],[[0]],[[-26838000]],[[0]],[[-3191760]],[[0]],[[-236952]],[[0]],[[-8856]],[[0]],[[-72]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
