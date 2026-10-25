/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode034
import Proofs.RadenkovicGutmanD18Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-54],[-54]],[[0,0],[0]],[[-972,-234],[-234]],[[0,0],[0]],[[-6804,-288],[-288]],[[0,0],[0]],[[-18792,-126],[-126]],[[0,0],[0]],[[-27252,-18],[-18]],[[0]],[[-22896]],[[0]],[[-11484]],[[0]],[[-3384]],[[0]],[[-540]],[[0]],[[-36]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
