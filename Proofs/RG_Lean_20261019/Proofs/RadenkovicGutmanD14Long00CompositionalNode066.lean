/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode065
import Proofs.RadenkovicGutmanD14Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-14]],[[0,0],[0,0]],[[-126,-210],[-210,-2]],[[0,0],[0]],[[-3504,-718],[-718]],[[0,0],[0]],[[-18476,-804],[-804]],[[0,0],[0]],[[-43226,-352],[-352]],[[0,0],[0]],[[-55444,-58],[-58]],[[0,0],[0]],[[-42376,-2],[-2]],[[0]],[[-19870]],[[0]],[[-5666]],[[0]],[[-930]],[[0]],[[-76]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
