/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode034
import Proofs.RadenkovicGutmanD18Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-540,0],[0]],[[0,0],[0]],[[-3384,0],[0]],[[0,0],[0]],[[-11484,0],[0]],[[0,0],[0]],[[-22896,0],[0]],[[0,0],[0]],[[-27252,-18],[-18]],[[0,0],[0]],[[-18792,-126],[-126]],[[0,0],[0]],[[-6804,-288],[-288]],[[0,0],[0]],[[-972,-234],[-234]],[[0,0],[0]],[[0,-54],[-54]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
