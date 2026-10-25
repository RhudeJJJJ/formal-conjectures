/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode071
import Proofs.RadenkovicGutmanD16Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-13824,0],[-13824,-3456,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-238464,-266112,0],[-266112,-39456,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4913568,-2156832,0],[-2156832,-184128,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-44733600,-9818432,0],[-9818432,-455712,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-239757312,-28155872,0],[-28155872,-654144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-849977632,-54017088,0],[-54017088,-564864,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2122626912,-71847776,0],[-71847776,-295104],[0]],[[0,0,0],[0,0],[0]],[[-3881635520,-67679360,0],[-67679360,-90912],[0]],[[0,0,0],[0,0],[0]],[[-5331578880,-45635904,0],[-45635904,-15168],[0]],[[0,0,0],[0,0],[0]],[[-5593347296,-22049792,0],[-22049792,-1056],[0]],[[0,0,0],[0,0],[0]],[[-4528971968,-7557728,0],[-7557728,0],[0]],[[0,0],[0]],[[-2845257408,-1791552],[-1791552]],[[0,0],[0]],[[-1387425920,-279008],[-279008]],[[0,0],[0]],[[-522613472,-25664],[-25664]],[[0,0],[0]],[[-150384096,-1056],[-1056]],[[0,0],[0]],[[-32408000,0],[0]],[[0]],[[-5058176]],[[0]],[[-539552]],[[0]],[[-35168]],[[0]],[[-1056]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
