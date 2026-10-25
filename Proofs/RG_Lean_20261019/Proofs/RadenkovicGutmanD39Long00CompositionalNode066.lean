/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode065
import Proofs.RadenkovicGutmanD39Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-39]],[[0,0],[0,0]],[[-351,-585],[-585,-2]],[[0,0],[0]],[[-9729,-1968],[-1968]],[[0,0],[0]],[[-50901,-2154],[-2154]],[[0,0],[0]],[[-117926,-902],[-902]],[[0,0],[0]],[[-149344,-133],[-133]],[[0,0],[0]],[[-112176,-2],[-2]],[[0]],[[-51295]],[[0]],[[-14066]],[[0]],[[-2155]],[[0]],[[-151]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
