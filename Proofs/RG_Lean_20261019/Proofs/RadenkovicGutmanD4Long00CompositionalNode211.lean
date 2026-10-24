/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode157
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e211 : NestedArithmetic.Expr 3 := .times e009 e157
noncomputable def p211 : NestedHorner.Poly 3 := [[[4],[0]],[[0,0],[0]],[[60,0],[0,0]],[[0,0],[0,0]],[[376,0],[0,0]],[[0,0],[0,0]],[[1276,0],[0,0]],[[0,0],[0,0]],[[2544,0],[0,0]],[[0,0],[0,0]],[[3024,4],[4,0]],[[0,0],[0,0]],[[2056,32],[32,0]],[[0,0],[0,0]],[[668,88],[88,0]],[[0,0],[0,0]],[[12,96],[96,0]],[[0,0],[0,0]],[[-36,36],[36,0]],[[0],[0,0]],[[0],[0,4]]]
theorem step211 : p211=NestedArithmetic.mul p009 p157 := by decide +kernel
#print axioms step211
theorem h211 : NestedArithmetic.compile e211=p211 := StagedExprCompile.compile_times e211 e009 e157 p009 p157 p211 rfl h009 h157 step211
#print axioms h211
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
