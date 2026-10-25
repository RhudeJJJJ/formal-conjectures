/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,324],[0,648],[324]],[[0,0,0],[0,0],[0]],[[0,10692,2808],[10692,5616],[2808]],[[0,0,0],[0,0],[0]],[[87480,119556,9540],[119556,19080],[9540]],[[0,0,0],[0,0],[0]],[[1195560,571212,16488],[571212,32976],[16488]],[[0,0,0],[0,0],[0]],[[7288056,1546200,15984],[1546200,31968],[15984]],[[0,0,0],[0,0],[0]],[[26381376,2654028,9000],[2654028,18000],[9000]],[[0,0,0],[0,0],[0]],[[63669456,3057732,2916],[3057732,5832],[2916]],[[0,0,0],[0,0],[0]],[[108940176,2434896,504],[2434896,1008],[504]],[[0,0,0],[0,0],[0]],[[137030616,1355724,36],[1355724,72],[36]],[[0,0],[0]],[[129526488,525924],[525924]],[[0,0],[0]],[[93158208,139176],[139176]],[[0,0],[0]],[[51241608,23940],[23940]],[[0,0],[0]],[[21521448,2412],[2412]],[[0,0],[0]],[[6841008,108],[108]],[[0]],[[1616112]],[[0]],[[274752]],[[0]],[[31752]],[[0]],[[2232]],[[0]],[[72]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
