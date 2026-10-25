/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode034
import Proofs.RadenkovicGutmanD30Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-60],[0]],[[0,0],[0]],[[-900,0],[0]],[[0,0],[0]],[[-5640,0],[0]],[[0,0],[0]],[[-19140,0],[0]],[[0,0],[0]],[[-38160,0],[0]],[[0,0],[0]],[[-45420,-30],[-30]],[[0,0],[0]],[[-31320,-210],[-210]],[[0,0],[0]],[[-11340,-480],[-480]],[[0,0],[0]],[[-1620,-390],[-390]],[[0,0],[0]],[[0,-90],[-90]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
