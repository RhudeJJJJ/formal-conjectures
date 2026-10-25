/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode071
import Proofs.RadenkovicGutmanD10Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-5400,0],[-5400,-1620,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-95580,-106380,0],[-106380,-17820,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1983960,-870660,0],[-870660,-80460,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18121860,-3975860,0],[-3975860,-193740,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-97217940,-11399900,0],[-11399900,-272280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-344509480,-21835980,0],[-21835980,-231480,0],[0,0]],[[0,0,0],[0,0],[0]],[[-859344420,-28981820,0],[-28981820,-119580],[0]],[[0,0,0],[0,0],[0]],[[-1569089480,-27238880,0],[-27238880,-36540],[0]],[[0,0,0],[0,0],[0]],[[-2151592620,-18327120,0],[-18327120,-6060],[0]],[[0,0,0],[0,0],[0]],[[-2253368660,-8837180,0],[-8837180,-420],[0]],[[0,0,0],[0,0],[0]],[[-1821509120,-3023420,0],[-3023420,0],[0]],[[0,0],[0]],[[-1142499000,-715500],[-715500]],[[0,0],[0]],[[-556270460,-111260],[-111260]],[[0,0],[0]],[[-209238320,-10220],[-10220]],[[0,0],[0]],[[-60129780,-420],[-420]],[[0,0],[0]],[[-12942200,0],[0]],[[0]],[[-2017700]],[[0]],[[-215000]],[[0]],[[-14000]],[[0]],[[-420]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
