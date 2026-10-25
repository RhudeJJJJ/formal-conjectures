/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode236
import Proofs.RadenkovicGutmanD17Long00CompositionalNode238
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e239 : NestedArithmetic.Expr 3 := .plus e236 e238
noncomputable def p239 : NestedHorner.Poly 3 := [[[-289],[0],[0]],[[0,0],[0,0],[0]],[[-9537,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-144789,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1340960,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8470590,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-38655773,-289,0],[-289,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-131699323,-6936,0],[-6936,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-341415352,-74273,0],[-74273,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-680239530,-468180,0],[-468180,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1045062726,-1930231,0],[-1930231,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1234879371,-5470770,0],[-5470770,-289,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1112972524,-10909172,0],[-10909172,-4046,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-753646686,-15408324,0],[-15408324,-23409,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-374292281,-15321913,0],[-15321913,-72250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-131276805,-10528848,0],[-10528848,-128316,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-30556548,-4830635,0],[-4830635,-132362,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4205817,-1394136,0],[-1394136,-76585,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-257499,-226287,0],[-226287,-22542,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-15606,0],[-15606,-2601,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step239 : p239=NestedHorner.add p236 p238 := by decide +kernel
#print axioms step239
theorem h239 : NestedArithmetic.compile e239=p239 := StagedExprCompile.compile_plus e239 e236 e238 p236 p238 p239 rfl h236 h238 step239
#print axioms h239
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
