/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode034
import Proofs.RadenkovicGutmanD12Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-360,0],[0]],[[0,0],[0]],[[-2256,0],[0]],[[0,0],[0]],[[-7656,0],[0]],[[0,0],[0]],[[-15264,0],[0]],[[0,0],[0]],[[-18168,-12],[-12]],[[0,0],[0]],[[-12528,-84],[-84]],[[0,0],[0]],[[-4536,-192],[-192]],[[0,0],[0]],[[-648,-156],[-156]],[[0,0],[0]],[[0,-36],[-36]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
