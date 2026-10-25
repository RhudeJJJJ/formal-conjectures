/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[72],[0],[0]],[[0,0],[0,0],[0]],[[2232,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[31752,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[274752,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1616112,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[6841008,108,0],[108,0],[0]],[[0,0,0],[0,0],[0]],[[21521448,2412,0],[2412,0],[0]],[[0,0,0],[0,0],[0]],[[51241608,23940,0],[23940,0],[0]],[[0,0,0],[0,0],[0]],[[93158208,139176,0],[139176,0],[0]],[[0,0,0],[0,0],[0]],[[129526488,525924,0],[525924,0],[0]],[[0,0,0],[0,0],[0]],[[137030616,1355724,36],[1355724,72],[36]],[[0,0,0],[0,0],[0]],[[108940176,2434896,504],[2434896,1008],[504]],[[0,0,0],[0,0],[0]],[[63669456,3057732,2916],[3057732,5832],[2916]],[[0,0,0],[0,0],[0]],[[26381376,2654028,9000],[2654028,18000],[9000]],[[0,0,0],[0,0],[0]],[[7288056,1546200,15984],[1546200,31968],[15984]],[[0,0,0],[0,0],[0]],[[1195560,571212,16488],[571212,32976],[16488]],[[0,0,0],[0,0],[0]],[[87480,119556,9540],[119556,19080],[9540]],[[0,0,0],[0,0],[0]],[[0,10692,2808],[10692,5616],[2808]],[[0,0,0],[0,0],[0]],[[0,0,324],[0,648],[324]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
