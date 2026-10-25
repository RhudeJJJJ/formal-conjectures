/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode065
import Proofs.RadenkovicGutmanD26Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-26]],[[0,0],[0,0]],[[-234,-390],[-390,-2]],[[0,0],[0]],[[-6492,-1318],[-1318]],[[0,0],[0]],[[-34040,-1452],[-1452]],[[0,0],[0]],[[-79082,-616],[-616]],[[0,0],[0]],[[-100516,-94],[-94]],[[0,0],[0]],[[-75880,-2],[-2]],[[0]],[[-34954]],[[0]],[[-9698]],[[0]],[[-1518]],[[0]],[[-112]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
