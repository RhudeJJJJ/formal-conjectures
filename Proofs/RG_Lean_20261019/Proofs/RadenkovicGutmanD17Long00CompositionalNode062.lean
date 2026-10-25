/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode044
import Proofs.RadenkovicGutmanD17Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,17]],[[0,0],[0,0]],[[153,153],[153,2]],[[0,0],[0]],[[2721,426],[426]],[[0,0],[0]],[[12167,422],[422]],[[0,0],[0]],[[25704,180],[180]],[[0,0],[0]],[[30808,33],[33]],[[0,0],[0]],[[22600,2],[2]],[[0]],[[10449]],[[0]],[[3036]],[[0]],[[533]],[[0]],[[51]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
