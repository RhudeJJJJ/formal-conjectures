/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode045
import Proofs.RadenkovicGutmanD44Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,44]],[[0,0],[0,0]],[[-396,660],[660,2]],[[0,0],[0]],[[4866,2218],[2218]],[[0,0],[0]],[[40618,2424],[2424]],[[0,0],[0]],[[114822,1012],[1012]],[[0,0],[0]],[[167524,148],[148]],[[0,0],[0]],[[141432,2],[2]],[[0]],[[71452]],[[0]],[[21318]],[[0]],[[3488]],[[0]],[[250]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
