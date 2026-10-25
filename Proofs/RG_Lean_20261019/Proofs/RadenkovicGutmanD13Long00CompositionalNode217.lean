/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode034
import Proofs.RadenkovicGutmanD13Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-390,0],[0]],[[0,0],[0]],[[-2444,0],[0]],[[0,0],[0]],[[-8294,0],[0]],[[0,0],[0]],[[-16536,0],[0]],[[0,0],[0]],[[-19682,-13],[-13]],[[0,0],[0]],[[-13572,-91],[-91]],[[0,0],[0]],[[-4914,-208],[-208]],[[0,0],[0]],[[-702,-169],[-169]],[[0,0],[0]],[[0,-39],[-39]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
