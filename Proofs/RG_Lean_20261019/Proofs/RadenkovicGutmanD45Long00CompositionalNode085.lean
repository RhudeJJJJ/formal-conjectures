/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode073
import Proofs.RadenkovicGutmanD45Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-3240,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29160,-466560,0],[-466560,-101790,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7992270,-6680070,0],[-6680070,-734220,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-125652870,-40760820,0],[-40760820,-2335230,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-899182080,-140209650,0],[-140209650,-3910860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3829228110,-303925860,0],[-303925860,-3726360,0],[0,0]],[[0,0,0],[0,0],[0]],[[-10852864290,-440433090,0],[-440433090,-2076660],[0]],[[0,0,0],[0,0],[0]],[[-21756876660,-441479160,0],[-441479160,-668430],[0]],[[0,0,0],[0,0],[0]],[[-32021375040,-311765940,0],[-311765940,-115020],[0]],[[0,0,0],[0,0],[0]],[[-35432414370,-156020760,0],[-156020760,-8190],[0]],[[0,0,0],[0,0],[0]],[[-29919238740,-54954090,0],[-54954090,0],[0]],[[0,0],[0]],[[-19438380900,-13310100],[-13310100]],[[0,0],[0]],[[-9740767320,-2108970],[-2108970]],[[0,0],[0]],[[-3752335890,-196740],[-196740]],[[0,0],[0]],[[-1100063610,-8190],[-8190]],[[0,0],[0]],[[-240804900,0],[0]],[[0]],[[-38086200]],[[0]],[[-4108950]],[[0]],[[-270450]],[[0]],[[-8190]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
