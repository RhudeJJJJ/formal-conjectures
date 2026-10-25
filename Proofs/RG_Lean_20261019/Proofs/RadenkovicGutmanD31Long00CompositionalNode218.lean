/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode034
import Proofs.RadenkovicGutmanD31Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-31],[0]],[[0,0],[0]],[[-496,0],[0]],[[0,0],[0]],[[-3317,0],[0]],[[0,0],[0]],[[-12028,0],[0]],[[0,0],[0]],[[-25668,0],[0]],[[0,0],[0]],[[-32736,-31],[-31]],[[0,0],[0]],[[-24149,-217],[-217]],[[0,0],[0]],[[-9300,-496],[-496]],[[0,0],[0]],[[-1395,-403],[-403]],[[0,0],[0]],[[0,-93],[-93]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
