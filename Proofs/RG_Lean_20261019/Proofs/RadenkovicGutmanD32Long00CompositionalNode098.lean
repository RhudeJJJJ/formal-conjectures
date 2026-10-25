/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3072],[0,3072]],[[0,0,0],[0,0,0],[0,0]],[[0,-27648,46080],[-27648,138240,13504],[46080,13504]],[[0,0,0],[0,0,0],[0,0]],[[-414720,914112,355008],[914112,1020096,17216],[355008,17216]],[[0,0,0],[0,0,0],[0,0]],[[2376000,11141568,1089344],[11141568,2995584,8192],[1089344,8192]],[[0,0,0],[0,0,0],[0,0]],[[70082496,52365440,1746560],[52365440,4624320,1472],[1746560,1472]],[[0,0,0],[0,0,0],[0,0]],[[487766784,137872832,1609024],[137872832,4133504,64],[1609024,64]],[[0,0,0],[0,0],[0]],[[1848409024,230801152,879360],[230801152,2209024],[879360]],[[0,0,0],[0,0],[0]],[[4551365824,260767040,282560],[260767040,699520],[282560]],[[0,0,0],[0,0],[0]],[[7870119552,204849024,50048],[204849024,123328],[50048]],[[0,0,0],[0,0],[0]],[[9967767296,113193664,4032],[113193664,10112],[4032]],[[0,0,0],[0,0],[0]],[[9475448768,43862080,64],[43862080,192],[64]],[[0,0],[0]],[[6853637376,11690880],[11690880]],[[0,0],[0]],[[3794043392,2052608],[2052608]],[[0,0],[0]],[[1605966848,217216],[217216]],[[0,0],[0]],[[515632960,11264],[11264]],[[0,0],[0]],[[123483840,128],[128]],[[0]],[[21413760]],[[0]],[[2554880]],[[0]],[[190784]],[[0]],[[7232]],[[0]],[[64]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
