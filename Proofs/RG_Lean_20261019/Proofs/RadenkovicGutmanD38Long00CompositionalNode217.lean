/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode034
import Proofs.RadenkovicGutmanD38Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-76],[0]],[[0,0],[0]],[[-1140,0],[0]],[[0,0],[0]],[[-7144,0],[0]],[[0,0],[0]],[[-24244,0],[0]],[[0,0],[0]],[[-48336,0],[0]],[[0,0],[0]],[[-57532,-38],[-38]],[[0,0],[0]],[[-39672,-266],[-266]],[[0,0],[0]],[[-14364,-608],[-608]],[[0,0],[0]],[[-2052,-494],[-494]],[[0,0],[0]],[[0,-114],[-114]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
