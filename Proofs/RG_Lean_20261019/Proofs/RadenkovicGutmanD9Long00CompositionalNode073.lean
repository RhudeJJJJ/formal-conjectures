/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode071
import Proofs.RadenkovicGutmanD9Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-4374,0],[-4374,-1377,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-78003,-86751,0],[-86751,-15012,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1622511,-711990,0],[-711990,-67221,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14834178,-3254175,0],[-3254175,-160704,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-79601589,-9330282,0],[-9330282,-224568,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-282049551,-17863677,0],[-17863677,-190098,0],[0,0]],[[0,0,0],[0,0],[0]],[[-703315368,-23695182,0],[-23695182,-97893],[0]],[[0,0,0],[0,0],[0]],[[-1283640624,-22255884,0],[-22255884,-29844],[0]],[[0,0,0],[0,0],[0]],[[-1759336731,-14965110,0],[-14965110,-4941],[0]],[[0,0,0],[0,0],[0]],[[-1841660784,-7211871,0],[-7211871,-342],[0]],[[0,0,0],[0,0],[0]],[[-1487993454,-2466054,0],[-2466054,0],[0]],[[0,0],[0]],[[-932881068,-583317],[-583317]],[[0,0],[0]],[[-454012803,-90666],[-90666]],[[0,0],[0]],[[-170705223,-8325],[-8325]],[[0,0],[0]],[[-49037760,-342],[-342]],[[0,0],[0]],[[-10551060,0],[0]],[[0]],[[-1644381]],[[0]],[[-175167]],[[0]],[[-11403]],[[0]],[[-342]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
