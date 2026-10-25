/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode058
import Proofs.RadenkovicGutmanD28Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-52]],[[0,0],[0]],[[-468,-468],[-468]],[[0,0],[0]],[[-8268,-1248],[-1248]],[[0,0],[0]],[[-36244,-1144],[-1144]],[[0,0],[0]],[[-74360,-416],[-416]],[[0,0],[0]],[[-85488,-52],[-52]],[[0]],[[-59072]],[[0]],[[-25012]],[[0]],[[-6344]],[[0]],[[-884]],[[0]],[[-52]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
