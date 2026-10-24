/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e032 : NestedArithmetic.Expr 3 := .times e009 e031
noncomputable def p032 : NestedHorner.Poly 3 := [[[0],[0,4]],[[0,0],[0]],[[-36,36],[36]],[[0,0],[0]],[[12,96],[96]],[[0,0],[0]],[[668,88],[88]],[[0,0],[0]],[[2056,32],[32]],[[0,0],[0]],[[3024,4],[4]],[[0]],[[2544]],[[0]],[[1276]],[[0]],[[376]],[[0]],[[60]],[[0]],[[4]]]
theorem step032 : p032=NestedArithmetic.mul p009 p031 := by decide +kernel
#print axioms step032
theorem h032 : NestedArithmetic.compile e032=p032 := StagedExprCompile.compile_times e032 e009 e031 p009 p031 p032 rfl h009 h031 step032
#print axioms h032
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
