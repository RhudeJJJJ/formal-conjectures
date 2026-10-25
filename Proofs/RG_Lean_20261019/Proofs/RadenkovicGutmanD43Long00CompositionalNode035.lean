/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode034
import Proofs.RadenkovicGutmanD43Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-129],[-129]],[[0,0],[0]],[[-2322,-559],[-559]],[[0,0],[0]],[[-16254,-688],[-688]],[[0,0],[0]],[[-44892,-301],[-301]],[[0,0],[0]],[[-65102,-43],[-43]],[[0]],[[-54696]],[[0]],[[-27434]],[[0]],[[-8084]],[[0]],[[-1290]],[[0]],[[-86]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
