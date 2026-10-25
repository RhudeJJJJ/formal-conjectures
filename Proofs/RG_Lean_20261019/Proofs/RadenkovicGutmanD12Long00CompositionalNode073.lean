/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode071
import Proofs.RadenkovicGutmanD12Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-7776,0],[-7776,-2160,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-136080,-151632,0],[-151632,-24120,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2815560,-1235736,0],[-1235736,-110400,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25680888,-5635296,0],[-5635296,-268920,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-137713680,-16158888,0],[-16158888,-381360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-488101992,-30973056,0],[-30973056,-326400,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1218132264,-41147400,0],[-41147400,-169440],[0]],[[0,0,0],[0,0],[0]],[[-2225680464,-38710944,0],[-38710944,-51960],[0]],[[0,0,0],[0,0],[0]],[[-3054168816,-26070672,0],[-26070672,-8640],[0]],[[0,0,0],[0,0],[0]],[[-3201031752,-12582192,0],[-12582192,-600],[0]],[[0,0,0],[0,0],[0]],[[-2589450288,-4308168,0],[-4308168,0],[0]],[[0,0],[0]],[[-1625313552,-1020288],[-1020288]],[[0,0],[0]],[[-791872848,-158760],[-158760]],[[0,0],[0]],[[-298044024,-14592],[-14592]],[[0,0],[0]],[[-85699848,-600],[-600]],[[0,0],[0]],[[-18455760,0],[0]],[[0]],[[-2878704]],[[0]],[[-306888]],[[0]],[[-19992]],[[0]],[[-600]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
