/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode065
import Proofs.RadenkovicGutmanD7Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-7]],[[0,0],[0,0]],[[-63,-105],[-105,-2]],[[0,0],[0]],[[-1761,-368],[-368]],[[0,0],[0]],[[-9397,-426],[-426]],[[0,0],[0]],[[-22310,-198],[-198]],[[0,0],[0]],[[-29152,-37],[-37]],[[0,0],[0]],[[-22832,-2],[-2]],[[0]],[[-11071]],[[0]],[[-3314]],[[0]],[[-587]],[[0]],[[-55]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
