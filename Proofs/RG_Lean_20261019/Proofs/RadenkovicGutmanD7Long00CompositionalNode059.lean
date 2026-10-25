/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode058
import Proofs.RadenkovicGutmanD7Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-10]],[[0,0],[0]],[[-90,-90],[-90]],[[0,0],[0]],[[-1590,-240],[-240]],[[0,0],[0]],[[-6970,-220],[-220]],[[0,0],[0]],[[-14300,-80],[-80]],[[0,0],[0]],[[-16440,-10],[-10]],[[0]],[[-11360]],[[0]],[[-4810]],[[0]],[[-1220]],[[0]],[[-170]],[[0]],[[-10]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
