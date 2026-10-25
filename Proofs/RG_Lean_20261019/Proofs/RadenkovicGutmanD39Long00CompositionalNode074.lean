/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode065
import Proofs.RadenkovicGutmanD39Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e074 : NestedArithmetic.Expr 3 := .times e065 e057
noncomputable def p074 : NestedHorner.Poly 3 := [[[0],[0]],[[0,117],[117]],[[0,0],[0]],[[1755,507],[507]],[[0,0],[0]],[[11700,624],[624]],[[0,0],[0]],[[30381,273],[273]],[[0,0],[0]],[[41184,39],[39]],[[0]],[[32292]],[[0]],[[15132]],[[0]],[[4173]],[[0]],[[624]],[[0]],[[39]]]
theorem step074 : p074=NestedArithmetic.mul p065 p057 := by decide +kernel
#print axioms step074
theorem h074 : NestedArithmetic.compile e074=p074 := StagedExprCompile.compile_times e074 e065 e057 p065 p057 p074 rfl h065 h057 step074
#print axioms h074
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
