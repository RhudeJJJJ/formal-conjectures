/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode065
import Proofs.RadenkovicGutmanD39Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-151,0],[0,0]],[[0,0],[0,0]],[[-2155,0],[0,0]],[[0,0],[0,0]],[[-14066,0],[0,0]],[[0,0],[0,0]],[[-51295,0],[0,0]],[[0,0],[0,0]],[[-112176,-2],[-2,0]],[[0,0],[0,0]],[[-149344,-133],[-133,0]],[[0,0],[0,0]],[[-117926,-902],[-902,0]],[[0,0],[0,0]],[[-50901,-2154],[-2154,0]],[[0,0],[0,0]],[[-9729,-1968],[-1968,0]],[[0,0],[0,0]],[[-351,-585],[-585,-2]],[[0],[0,0]],[[0],[0,-39]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
