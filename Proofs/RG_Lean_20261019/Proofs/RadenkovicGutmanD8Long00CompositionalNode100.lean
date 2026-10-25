/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode043
import Proofs.RadenkovicGutmanD8Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-576],[0,-1152,288],[-576,288]],[[0,0,0],[0,0,0],[0,0]],[[0,-23328,-2400],[-23328,-480,1248],[-2400,1248]],[[0,0,0],[0,0,0],[0,0]],[[-220320,-206496,1184],[-206496,31168,1536],[1184,1536]],[[0,0,0],[0,0,0],[0,0]],[[-2769120,-739584,20800],[-739584,116384,672],[20800,672]],[[0,0,0],[0,0,0],[0,0]],[[-15531264,-1326816,44256],[-1326816,189888,96],[44256,96]],[[0,0,0],[0,0],[0]],[[-51462240,-999232,45056],[-999232,169600],[45056]],[[0,0,0],[0,0],[0]],[[-112076000,610976,25440],[610976,88128],[25440]],[[0,0,0],[0,0],[0]],[[-168224576,2279488,8128],[2279488,26528],[8128]],[[0,0,0],[0,0],[0]],[[-176141568,2615904,1376],[2615904,4288],[1376]],[[0,0,0],[0,0],[0]],[[-124839904,1758496,96],[1758496,288],[96]],[[0,0],[0]],[[-51556480,765120],[765120]],[[0,0],[0]],[[-918400,218560],[218560]],[[0,0],[0]],[[15014272,39680],[39680]],[[0,0],[0]],[[11514336,4160],[4160]],[[0,0],[0]],[[5008416,192],[192]],[[0]],[[1446720]],[[0]],[[283520]],[[0]],[[36448]],[[0]],[[2784]],[[0]],[[96]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
