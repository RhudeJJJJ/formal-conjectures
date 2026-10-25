/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode049
import Proofs.RadenkovicGutmanD30Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,30]],[[0,0],[0,0]],[[-270,450],[450,2]],[[0,0],[0]],[[3348,1518],[1518]],[[0,0],[0]],[[28008,1668],[1668]],[[0,0],[0]],[[79454,704],[704]],[[0,0],[0]],[[116380,106],[106]],[[0,0],[0]],[[98688,2],[2]],[[0]],[[50122]],[[0]],[[15062]],[[0]],[[2494]],[[0]],[[184]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
