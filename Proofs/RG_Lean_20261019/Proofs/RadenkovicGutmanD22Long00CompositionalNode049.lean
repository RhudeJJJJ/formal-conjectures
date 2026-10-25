/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode045
import Proofs.RadenkovicGutmanD22Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,22]],[[0,0],[0,0]],[[-198,330],[330,2]],[[0,0],[0]],[[2424,1118],[1118]],[[0,0],[0]],[[20312,1236],[1236]],[[0,0],[0]],[[57578,528],[528]],[[0,0],[0]],[[84276,82],[82]],[[0,0],[0]],[[71472,2],[2]],[[0]],[[36362]],[[0]],[[10978]],[[0]],[[1838]],[[0]],[[140]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
