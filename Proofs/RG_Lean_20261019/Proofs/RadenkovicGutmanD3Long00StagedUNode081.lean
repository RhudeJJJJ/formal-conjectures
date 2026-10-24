/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode068
import Proofs.RadenkovicGutmanD3Long00StagedUNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e068 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,72],[0,72,16]],[[0,0,0],[0,0,0],[0,0,0]],[[0,648,972],[648,3096,672],[972,672,4]],[[0,0,0],[0,0,0],[0,0]],[[9072,35964,9288],[35964,30252,1536],[9288,1536]],[[0,0,0],[0,0,0],[0,0]],[[329616,369792,33840],[369792,111728,1448],[33840,1448]],[[0,0,0],[0,0,0],[0,0]],[[3634740,1759452,64464],[1759452,216492,624],[64464,624]],[[0,0,0],[0,0,0],[0,0]],[[20755812,4899612,72504],[4899612,249112,120],[72504,120]],[[0,0,0],[0,0,0],[0,0]],[[74021212,8879972,50896],[8879972,179808,8],[50896,8]],[[0,0,0],[0,0],[0]],[[180981776,11090920,22772],[11090920,82960],[22772]],[[0,0,0],[0,0],[0]],[[320240120,9861792,6448],[9861792,24236],[6448]],[[0,0,0],[0,0],[0]],[[424202720,6352404,1108],[6352404,4288],[1108]],[[0,0,0],[0,0],[0]],[[429897548,2982708,104],[2982708,412],[104]],[[0,0,0],[0,0],[0]],[[337884216,1016740,4],[1016740,16],[4]],[[0,0],[0]],[[207525264,247676],[247676]],[[0,0],[0]],[[99850872,41752],[41752]],[[0,0],[0]],[[37546548,4588],[4588]],[[0,0],[0]],[[10948768,292],[292]],[[0,0],[0]],[[2440584,8],[8]],[[0]],[[406144]],[[0]],[[48564]],[[0]],[[3912]],[[0]],[[188]],[[0]],[[4]]]
theorem step081 : p081=NestedHorner.add p068 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e068 e080 p068 p080 p081 rfl h068 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
