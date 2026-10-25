/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode065
import Proofs.RadenkovicGutmanD29Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e074 : NestedArithmetic.Expr 3 := .times e065 e057
noncomputable def p074 : NestedHorner.Poly 3 := [[[0],[0]],[[0,87],[87]],[[0,0],[0]],[[1305,377],[377]],[[0,0],[0]],[[8700,464],[464]],[[0,0],[0]],[[22591,203],[203]],[[0,0],[0]],[[30624,29],[29]],[[0]],[[24012]],[[0]],[[11252]],[[0]],[[3103]],[[0]],[[464]],[[0]],[[29]]]
theorem step074 : p074=NestedArithmetic.mul p065 p057 := by decide +kernel
#print axioms step074
theorem h074 : NestedArithmetic.compile e074=p074 := StagedExprCompile.compile_times e074 e065 e057 p065 p057 p074 rfl h065 h057 step074
#print axioms h074
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
