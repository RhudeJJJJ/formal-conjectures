/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode034
import Proofs.RadenkovicGutmanD4Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e034 e063
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-48],[0,-48]],[[0,0,0],[0,0,0],[0,0]],[[0,-432,-720],[-432,-2304,-232],[-720,-232]],[[0,0,0],[0,0,0],[0,0]],[[-7776,-27000,-5736],[-27000,-17952,-360],[-5736,-360]],[[0,0,0],[0,0,0],[0,0]],[[-273456,-258912,-18344],[-258912,-56416,-240],[-18344,-240]],[[0,0,0],[0,0,0],[0,0]],[[-2872800,-1149568,-30944],[-1149568,-94464,-72],[-30944,-72]],[[0,0,0],[0,0,0],[0,0]],[[-15660288,-2990928,-30440],[-2990928,-93344,-8],[-30440,-8]],[[0,0,0],[0,0],[0]],[[-53359104,-5049392,-18192],[-5049392,-56768],[-18192]],[[0,0,0],[0,0],[0]],[[-124491440,-5834688,-6648],[-5834688,-21408],[-6648]],[[0,0,0],[0,0],[0]],[[-209570560,-4750624,-1440],[-4750624,-4864],[-1440]],[[0,0,0],[0,0],[0]],[[-262932064,-2763096,-168],[-2763096,-608],[-168]],[[0,0,0],[0,0],[0]],[[-250927312,-1149848,-8],[-1149848,-32],[-8]],[[0,0],[0]],[[-184410992,-338664],[-338664]],[[0,0],[0]],[[-105001008,-68704],[-68704]],[[0,0],[0]],[[-46346048,-9096],[-9096]],[[0,0],[0]],[[-15777952,-704],[-704]],[[0,0],[0]],[[-4094800,-24],[-24]],[[0]],[[-793568]],[[0]],[[-110944]],[[0]],[[-10544]],[[0]],[[-608]],[[0]],[[-16]]]
theorem step089 : p089=NestedArithmetic.mul p034 p063 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e034 e063 p034 p063 p089 rfl h034 h063 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
