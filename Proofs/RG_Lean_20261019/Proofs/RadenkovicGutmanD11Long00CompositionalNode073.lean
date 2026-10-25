/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode071
import Proofs.RadenkovicGutmanD11Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-6534,0],[-6534,-1881,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-114939,-128007,0],[-128007,-20856,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2381643,-1045242,0],[-1045242,-94853,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21737430,-4769567,0],[-4769567,-229812,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-116588637,-13676102,0],[-13676102,-324544,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-413193627,-26205773,0],[-26205773,-276914,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1030950052,-34799226,0],[-34799226,-143429],[0]],[[0,0,0],[0,0],[0]],[[-1883102760,-32723900,0],[-32723900,-43912],[0]],[[0,0,0],[0,0],[0]],[[-2583203315,-22028974,0],[-22028974,-7293],[0]],[[0,0,0],[0,0],[0]],[[-2706492316,-10627287,0],[-10627287,-506],[0]],[[0,0,0],[0,0],[0]],[[-2188661398,-3637458,0],[-3637458,0],[0]],[[0,0],[0]],[[-1373309828,-861157],[-861157]],[[0,0],[0]],[[-668890475,-133958],[-133958]],[[0,0],[0]],[[-251684587,-12309],[-12309]],[[0,0],[0]],[[-72350476,-506],[-506]],[[0,0],[0]],[[-15577100,0],[0]],[[0]],[[-2429141]],[[0]],[[-258907]],[[0]],[[-16863]],[[0]],[[-506]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
