/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode034
import Proofs.RadenkovicGutmanD12Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-192,0],[0]],[[0,0],[0]],[[-1284,0],[0]],[[0,0],[0]],[[-4656,0],[0]],[[0,0],[0]],[[-9936,0],[0]],[[0,0],[0]],[[-12672,-12],[-12]],[[0,0],[0]],[[-9348,-84],[-84]],[[0,0],[0]],[[-3600,-192],[-192]],[[0,0],[0]],[[-540,-156],[-156]],[[0,0],[0]],[[0,-36],[-36]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
