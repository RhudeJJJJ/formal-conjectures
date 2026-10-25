/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode065
import Proofs.RadenkovicGutmanD38Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e074 : NestedArithmetic.Expr 3 := .times e065 e057
noncomputable def p074 : NestedHorner.Poly 3 := [[[0],[0]],[[0,114],[114]],[[0,0],[0]],[[1710,494],[494]],[[0,0],[0]],[[11400,608],[608]],[[0,0],[0]],[[29602,266],[266]],[[0,0],[0]],[[40128,38],[38]],[[0]],[[31464]],[[0]],[[14744]],[[0]],[[4066]],[[0]],[[608]],[[0]],[[38]]]
theorem step074 : p074=NestedArithmetic.mul p065 p057 := by decide +kernel
#print axioms step074
theorem h074 : NestedArithmetic.compile e074=p074 := StagedExprCompile.compile_times e074 e065 e057 p065 p057 p074 rfl h065 h057 step074
#print axioms h074
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
