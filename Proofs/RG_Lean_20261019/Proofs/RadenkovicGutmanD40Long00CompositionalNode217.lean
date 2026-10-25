/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode034
import Proofs.RadenkovicGutmanD40Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-80],[0]],[[0,0],[0]],[[-1200,0],[0]],[[0,0],[0]],[[-7520,0],[0]],[[0,0],[0]],[[-25520,0],[0]],[[0,0],[0]],[[-50880,0],[0]],[[0,0],[0]],[[-60560,-40],[-40]],[[0,0],[0]],[[-41760,-280],[-280]],[[0,0],[0]],[[-15120,-640],[-640]],[[0,0],[0]],[[-2160,-520],[-520]],[[0,0],[0]],[[0,-120],[-120]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
