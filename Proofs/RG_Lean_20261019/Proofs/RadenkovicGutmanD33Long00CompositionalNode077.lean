/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,9801],[0,19602],[9801]],[[0,0,0],[0,0],[0]],[[0,323433,84942],[323433,169884],[84942]],[[0,0,0],[0,0],[0]],[[2646270,3616569,288585],[3616569,577170],[288585]],[[0,0,0],[0,0],[0]],[[36165690,17279163,498762],[17279163,997524],[498762]],[[0,0,0],[0,0],[0]],[[220463694,46772550,483516],[46772550,967032],[483516]],[[0,0,0],[0,0],[0]],[[798036624,80284347,272250],[80284347,544500],[272250]],[[0,0,0],[0,0],[0]],[[1926001044,92496393,88209],[92496393,176418],[88209]],[[0,0,0],[0,0],[0]],[[3295440324,73655604,15246],[73655604,30492],[15246]],[[0,0,0],[0,0],[0]],[[4145176134,41010651,1089],[41010651,2178],[1089]],[[0,0],[0]],[[3918176262,15909201],[15909201]],[[0,0],[0]],[[2818035792,4210074],[4210074]],[[0,0],[0]],[[1550058642,724185],[724185]],[[0,0],[0]],[[651023802,72963],[72963]],[[0,0],[0]],[[206940492,3267],[3267]],[[0]],[[48887388]],[[0]],[[8311248]],[[0]],[[960498]],[[0]],[[67518]],[[0]],[[2178]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
