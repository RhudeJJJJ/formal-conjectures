/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode034
import Proofs.RadenkovicGutmanD38Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-38],[0]],[[0,0],[0]],[[-608,0],[0]],[[0,0],[0]],[[-4066,0],[0]],[[0,0],[0]],[[-14744,0],[0]],[[0,0],[0]],[[-31464,0],[0]],[[0,0],[0]],[[-40128,-38],[-38]],[[0,0],[0]],[[-29602,-266],[-266]],[[0,0],[0]],[[-11400,-608],[-608]],[[0,0],[0]],[[-1710,-494],[-494]],[[0,0],[0]],[[0,-114],[-114]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
