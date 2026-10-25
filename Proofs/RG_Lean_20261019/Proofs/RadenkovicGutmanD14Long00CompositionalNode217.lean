/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode034
import Proofs.RadenkovicGutmanD14Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-420,0],[0]],[[0,0],[0]],[[-2632,0],[0]],[[0,0],[0]],[[-8932,0],[0]],[[0,0],[0]],[[-17808,0],[0]],[[0,0],[0]],[[-21196,-14],[-14]],[[0,0],[0]],[[-14616,-98],[-98]],[[0,0],[0]],[[-5292,-224],[-224]],[[0,0],[0]],[[-756,-182],[-182]],[[0,0],[0]],[[0,-42],[-42]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
