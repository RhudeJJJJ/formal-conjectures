/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode034
import Proofs.RadenkovicGutmanD28Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-448,0],[0]],[[0,0],[0]],[[-2996,0],[0]],[[0,0],[0]],[[-10864,0],[0]],[[0,0],[0]],[[-23184,0],[0]],[[0,0],[0]],[[-29568,-28],[-28]],[[0,0],[0]],[[-21812,-196],[-196]],[[0,0],[0]],[[-8400,-448],[-448]],[[0,0],[0]],[[-1260,-364],[-364]],[[0,0],[0]],[[0,-84],[-84]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
