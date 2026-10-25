/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode191
import Proofs.RadenkovicGutmanD37Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[71,0],[0,0]],[[0,0],[0,0]],[[873,0],[0,0]],[[0,0],[0,0]],[[5476,0],[0,0]],[[0,0],[0,0]],[[20069,0],[0,0]],[[0,0],[0,0]],[[45320,2],[2,0]],[[0,0],[0,0]],[[63688,53],[53,0]],[[0,0],[0,0]],[[54304,340],[340,0]],[[0,0],[0,0]],[[26107,862],[862,0]],[[0,0],[0,0]],[[5901,906],[906,0]],[[0,0],[0,0]],[[333,333],[333,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
