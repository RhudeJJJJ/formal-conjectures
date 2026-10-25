/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode034
import Proofs.RadenkovicGutmanD36Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-576,0],[0]],[[0,0],[0]],[[-3852,0],[0]],[[0,0],[0]],[[-13968,0],[0]],[[0,0],[0]],[[-29808,0],[0]],[[0,0],[0]],[[-38016,-36],[-36]],[[0,0],[0]],[[-28044,-252],[-252]],[[0,0],[0]],[[-10800,-576],[-576]],[[0,0],[0]],[[-1620,-468],[-468]],[[0,0],[0]],[[0,-108],[-108]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
