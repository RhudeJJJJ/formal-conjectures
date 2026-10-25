/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode043
import Proofs.RadenkovicGutmanD30Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,8100],[0,16200,-10080],[8100,-10080,3136]],[[0,0,0],[0,0,0],[0,0]],[[0,273780,-20520],[273780,-211392,12768],[-20520,12768]],[[0,0,0],[0,0,0],[0,0]],[[1857816,723492,-142524],[723492,-951000,96768],[-142524,96768]],[[0,0,0],[0,0,0],[0,0]],[[10190232,-3225636,13032],[-3225636,-445792,114464],[13032,114464]],[[0,0,0],[0,0,0],[0,0]],[[-12882888,-16873176,904272],[-16873176,3382144,46816],[904272,46816]],[[0,0,0],[0,0,0],[0,0]],[[-271549104,-23608164,1851240],[-23608164,7501968,6272],[1851240,6272]],[[0,0,0],[0,0],[0]],[[-1094395664,12279812,1779556],[12279812,7280424],[1779556]],[[0,0,0],[0,0],[0]],[[-2403218000,87549200,951160],[87549200,3879232],[951160]],[[0,0,0],[0,0],[0]],[[-3268432808,141099196,289188],[141099196,1172200],[289188]],[[0,0,0],[0,0],[0]],[[-2658249752,129405332,46816],[129405332,188496],[46816]],[[0,0,0],[0,0],[0]],[[-780749408,76999960,3136],[76999960,12544],[3136]],[[0,0],[0]],[[986675720,30791220],[30791220]],[[0,0],[0]],[[1611461800,8237420],[8237420]],[[0,0],[0]],[[1253108192,1416380],[1416380]],[[0,0],[0]],[[641651536,141680],[141680]],[[0,0],[0]],[[231685536,6272],[6272]],[[0]],[[59719560]],[[0]],[[10801000]],[[0]],[[1305608]],[[0]],[[94864]],[[0]],[[3136]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
