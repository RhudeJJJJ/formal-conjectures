/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode037
import Proofs.RadenkovicGutmanD4Long00CompositionalNode038
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e039 : NestedArithmetic.Expr 3 := .plus e037 e038
noncomputable def p039 : NestedHorner.Poly 3 := [[[0],[0,-2]],[[0,0],[0]],[[54,-18],[-18]],[[0,0],[0]],[[306,-48],[-48]],[[0,0],[0]],[[726,-44],[-44]],[[0,0],[0]],[[804,-16],[-16]],[[0,0],[0]],[[264,-2],[-2]],[[0]],[[-272]],[[0]],[[-314]],[[0]],[[-132]],[[0]],[[-26]],[[0]],[[-2]]]
theorem step039 : p039=NestedHorner.add p037 p038 := by decide +kernel
#print axioms step039
theorem h039 : NestedArithmetic.compile e039=p039 := StagedExprCompile.compile_plus e039 e037 e038 p037 p038 p039 rfl h037 h038 step039
#print axioms h039
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
