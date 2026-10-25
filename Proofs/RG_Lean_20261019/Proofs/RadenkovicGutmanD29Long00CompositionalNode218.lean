/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode034
import Proofs.RadenkovicGutmanD29Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-29],[0]],[[0,0],[0]],[[-464,0],[0]],[[0,0],[0]],[[-3103,0],[0]],[[0,0],[0]],[[-11252,0],[0]],[[0,0],[0]],[[-24012,0],[0]],[[0,0],[0]],[[-30624,-29],[-29]],[[0,0],[0]],[[-22591,-203],[-203]],[[0,0],[0]],[[-8700,-464],[-464]],[[0,0],[0]],[[-1305,-377],[-377]],[[0,0],[0]],[[0,-87],[-87]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
