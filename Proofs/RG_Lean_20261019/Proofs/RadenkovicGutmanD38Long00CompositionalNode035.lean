/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode034
import Proofs.RadenkovicGutmanD38Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-114],[-114]],[[0,0],[0]],[[-2052,-494],[-494]],[[0,0],[0]],[[-14364,-608],[-608]],[[0,0],[0]],[[-39672,-266],[-266]],[[0,0],[0]],[[-57532,-38],[-38]],[[0]],[[-48336]],[[0]],[[-24244]],[[0]],[[-7144]],[[0]],[[-1140]],[[0]],[[-76]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
