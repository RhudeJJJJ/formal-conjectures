/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode073
import Proofs.RadenkovicGutmanD35Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2520,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22680,-287280,0],[-287280,-66570,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4968810,-4099410,0],[-4099410,-461860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-77355810,-24949260,0],[-24949260,-1445290,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-551339040,-85650950,0],[-85650950,-2400580,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2342345530,-185381980,0],[-185381980,-2276680,0],[0,0]],[[0,0,0],[0,0],[0]],[[-6627936070,-268335270,0],[-268335270,-1265180],[0]],[[0,0,0],[0,0],[0]],[[-13271131580,-268730280,0],[-268730280,-406490],[0]],[[0,0,0],[0,0],[0]],[[-19513951520,-189637420,0],[-189637420,-69860],[0]],[[0,0,0],[0,0],[0]],[[-21576429910,-94847480,0],[-94847480,-4970],[0]],[[0,0,0],[0,0],[0]],[[-18207931420,-33391470,0],[-33391470,0],[0]],[[0,0],[0]],[[-11823462700,-8084300],[-8084300]],[[0,0],[0]],[[-5922237160,-1280510],[-1280510]],[[0,0],[0]],[[-2280493670,-119420],[-119420]],[[0,0],[0]],[[-668345230,-4970],[-4970]],[[0,0],[0]],[[-146258700,0],[0]],[[0]],[[-23126600]],[[0]],[[-2494450]],[[0]],[[-164150]],[[0]],[[-4970]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
