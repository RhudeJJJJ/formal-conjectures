/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode202
import Proofs.RadenkovicGutmanD37Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[71,0],[0,0]],[[0,0],[0,0]],[[873,0],[0,0]],[[0,0],[0,0]],[[5476,0],[0,0]],[[0,0],[0,0]],[[20069,0],[0,0]],[[0,0],[0,0]],[[45320,2],[2,0]],[[0,0],[0,0]],[[63688,53],[53,0]],[[0,0],[0,0]],[[54304,340],[340,0]],[[0,0],[0,0]],[[26107,862],[862,0]],[[0,0],[0,0]],[[5901,906],[906,0]],[[0,0],[0,0]],[[333,333],[333,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
