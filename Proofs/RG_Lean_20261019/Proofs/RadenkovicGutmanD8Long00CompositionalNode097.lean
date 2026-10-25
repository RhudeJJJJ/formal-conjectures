/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode051
import Proofs.RadenkovicGutmanD8Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-192],[0,-192]],[[0,0,0],[0,0,0],[0,0]],[[0,1728,-2880],[1728,-8640,-880],[-2880,-880]],[[0,0,0],[0,0,0],[0,0]],[[25920,-57456,-22512],[-57456,-64944,-1232],[-22512,-1232]],[[0,0,0],[0,0,0],[0,0]],[[-153360,-708336,-70352],[-708336,-195360,-704],[-70352,-704]],[[0,0,0],[0,0,0],[0,0]],[[-4498416,-3369824,-115424],[-3369824,-310896,-176],[-115424,-176]],[[0,0,0],[0,0,0],[0,0]],[[-31518336,-8990960,-109648],[-8990960,-289184,-16],[-109648,-16]],[[0,0,0],[0,0],[0]],[[-120407344,-15276544,-62592],[-15276544,-163264],[-62592]],[[0,0,0],[0,0],[0]],[[-299115952,-17558864,-21488],[-17558864,-56032],[-21488]],[[0,0,0],[0,0],[0]],[[-522236064,-14079264,-4256],[-14079264,-11248],[-4256]],[[0,0,0],[0,0],[0]],[[-668501120,-7980016,-432],[-7980016,-1184],[-432]],[[0,0,0],[0,0],[0]],[[-643124720,-3195664,-16],[-3195664,-48],[-16]],[[0,0],[0]],[[-471610944,-890976],[-890976]],[[0,0],[0]],[[-265338752,-167168],[-167168]],[[0,0],[0]],[[-114543680,-19744],[-19744]],[[0,0],[0]],[[-37694992,-1280],[-1280]],[[0,0],[0]],[[-9322800,-32],[-32]],[[0]],[[-1690080]],[[0]],[[-215360]],[[0]],[[-17936]],[[0]],[[-848]],[[0]],[[-16]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
