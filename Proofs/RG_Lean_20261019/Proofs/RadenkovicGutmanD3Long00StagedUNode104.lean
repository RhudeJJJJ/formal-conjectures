/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode093
import Proofs.RadenkovicGutmanD3Long00StagedUNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e093 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1944,-1944,0],[-1944,-1872,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-51192,-22032,0],[-22032,-6360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-505440,-106920,0],[-106920,-10992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2723832,-294480,0],[-294480,-10656,0],[0,0]],[[0,0,0],[0,0],[0]],[[-9308616,-514824,0],[-514824,-6000],[0]],[[0,0,0],[0,0],[0]],[[-21827472,-604320,0],[-604320,-1944],[0]],[[0,0,0],[0,0],[0]],[[-36803616,-490224,0],[-490224,-336],[0]],[[0,0,0],[0,0],[0]],[[-45954792,-277920,0],[-277920,-24],[0]],[[0,0,0],[0,0],[0]],[[-43285200,-109704,0],[-109704,0],[0]],[[0,0],[0]],[[-31082256,-29520],[-29520]],[[0,0],[0]],[[-17085696,-5160],[-5160]],[[0,0],[0]],[[-7174344,-528],[-528]],[[0,0],[0]],[[-2280360,-24],[-24]],[[0,0],[0]],[[-538704,0],[0]],[[0]],[[-91584]],[[0]],[[-10584]],[[0]],[[-744]],[[0]],[[-24]],[[0]],[[0]]]
theorem step104 : p104=NestedHorner.add p093 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e093 e103 p093 p103 p104 rfl h093 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
