/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode058
import Proofs.RadenkovicGutmanD43Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-82]],[[0,0],[0]],[[-738,-738],[-738]],[[0,0],[0]],[[-13038,-1968],[-1968]],[[0,0],[0]],[[-57154,-1804],[-1804]],[[0,0],[0]],[[-117260,-656],[-656]],[[0,0],[0]],[[-134808,-82],[-82]],[[0]],[[-93152]],[[0]],[[-39442]],[[0]],[[-10004]],[[0]],[[-1394]],[[0]],[[-82]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
