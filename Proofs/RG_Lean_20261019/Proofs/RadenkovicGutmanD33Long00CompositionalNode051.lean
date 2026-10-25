/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode049
import Proofs.RadenkovicGutmanD33Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,33]],[[0,0],[0,0]],[[-297,495],[495,2]],[[0,0],[0]],[[3681,1668],[1668]],[[0,0],[0]],[[30777,1830],[1830]],[[0,0],[0]],[[87260,770],[770]],[[0,0],[0]],[[127732,115],[115]],[[0,0],[0]],[[108228,2],[2]],[[0]],[[54907]],[[0]],[[16472]],[[0]],[[2719]],[[0]],[[199]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
