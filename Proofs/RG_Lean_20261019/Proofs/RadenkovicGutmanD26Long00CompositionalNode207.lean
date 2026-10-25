/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode065
import Proofs.RadenkovicGutmanD26Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-112,0],[0,0]],[[0,0],[0,0]],[[-1518,0],[0,0]],[[0,0],[0,0]],[[-9698,0],[0,0]],[[0,0],[0,0]],[[-34954,0],[0,0]],[[0,0],[0,0]],[[-75880,-2],[-2,0]],[[0,0],[0,0]],[[-100516,-94],[-94,0]],[[0,0],[0,0]],[[-79082,-616],[-616,0]],[[0,0],[0,0]],[[-34040,-1452],[-1452,0]],[[0,0],[0,0]],[[-6492,-1318],[-1318,0]],[[0,0],[0,0]],[[-234,-390],[-390,-2]],[[0],[0,0]],[[0],[0,-26]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
