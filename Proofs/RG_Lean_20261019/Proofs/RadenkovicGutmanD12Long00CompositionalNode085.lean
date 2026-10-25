/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode073
import Proofs.RadenkovicGutmanD12Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-864,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7776,-38880,0],[-38880,-12888,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-719928,-541080,0],[-541080,-72240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10455480,-3228336,0],[-3228336,-202968,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-72302400,-10912680,0],[-10912680,-317424,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-301603416,-23338608,0],[-23338608,-290400,0],[0,0]],[[0,0,0],[0,0],[0]],[[-842612808,-33469896,0],[-33469896,-157776],[0]],[[0,0,0],[0,0],[0]],[[-1671119760,-33275232,0],[-33275232,-49944],[0]],[[0,0,0],[0,0],[0]],[[-2438865600,-23344752,0],[-23344752,-8496],[0]],[[0,0,0],[0,0],[0]],[[-2680308456,-11620416,0],[-11620416,-600],[0]],[[0,0,0],[0,0],[0]],[[-2250507408,-4074888,0],[-4074888,0],[0]],[[0,0],[0]],[[-1455196560,-983280],[-983280]],[[0,0],[0]],[[-726251040,-155304],[-155304]],[[0,0],[0]],[[-278783016,-14448],[-14448]],[[0,0],[0]],[[-81479208,-600],[-600]],[[0,0],[0]],[[-17787600,0],[0]],[[0]],[[-2806560]],[[0]],[[-302136]],[[0]],[[-19848]],[[0]],[[-600]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
