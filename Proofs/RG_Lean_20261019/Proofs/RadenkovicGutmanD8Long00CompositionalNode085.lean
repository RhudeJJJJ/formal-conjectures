/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode073
import Proofs.RadenkovicGutmanD8Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-576,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5184,-19008,0],[-19008,-7440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-365904,-260496,0],[-260496,-38176,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5107536,-1534752,0],[-1534752,-101392,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34667904,-5135600,0],[-5135600,-152992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-142925584,-10895776,0],[-10895776,-136768,0],[0,0]],[[0,0,0],[0,0],[0]],[[-395965360,-15527088,0],[-15527088,-73184],[0]],[[0,0,0],[0,0],[0]],[[-780284768,-15359040,0],[-15359040,-22928],[0]],[[0,0,0],[0,0],[0]],[[-1132967552,-10731424,0],[-10731424,-3872],[0]],[[0,0,0],[0,0],[0]],[[-1239936112,-5323904,0],[-5323904,-272],[0]],[[0,0,0],[0,0],[0]],[[-1037473120,-1861680,0],[-1861680,0],[0]],[[0,0],[0]],[[-668848480,-448160],[-448160]],[[0,0],[0]],[[-332952256,-70640],[-70640]],[[0,0],[0]],[[-127524848,-6560],[-6560]],[[0,0],[0]],[[-37198576,-272],[-272]],[[0,0],[0]],[[-8106720,0],[0]],[[0]],[[-1277120]],[[0]],[[-137296]],[[0]],[[-9008]],[[0]],[[-272]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
