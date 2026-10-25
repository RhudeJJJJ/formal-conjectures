/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode034
import Proofs.RadenkovicGutmanD16Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-256,0],[0]],[[0,0],[0]],[[-1712,0],[0]],[[0,0],[0]],[[-6208,0],[0]],[[0,0],[0]],[[-13248,0],[0]],[[0,0],[0]],[[-16896,-16],[-16]],[[0,0],[0]],[[-12464,-112],[-112]],[[0,0],[0]],[[-4800,-256],[-256]],[[0,0],[0]],[[-720,-208],[-208]],[[0,0],[0]],[[0,-48],[-48]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
