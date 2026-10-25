/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode034
import Proofs.RadenkovicGutmanD44Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-88],[0]],[[0,0],[0]],[[-1320,0],[0]],[[0,0],[0]],[[-8272,0],[0]],[[0,0],[0]],[[-28072,0],[0]],[[0,0],[0]],[[-55968,0],[0]],[[0,0],[0]],[[-66616,-44],[-44]],[[0,0],[0]],[[-45936,-308],[-308]],[[0,0],[0]],[[-16632,-704],[-704]],[[0,0],[0]],[[-2376,-572],[-572]],[[0,0],[0]],[[0,-132],[-132]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
