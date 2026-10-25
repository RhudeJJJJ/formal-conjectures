/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,441],[0,882,-420],[441,-420,100]],[[0,0,0],[0,0,0],[0,0]],[[0,22680,42],[22680,-10716,-20],[42,-20]],[[0,0,0],[0,0,0],[0,0]],[[291600,137160,-5375],[137160,-75550,2560],[-5375,2560]],[[0,0,0],[0,0,0],[0,0]],[[3499200,194076,-7438],[194076,-170036,3420],[-7438,3420]],[[0,0,0],[0,0,0],[0,0]],[[18876240,-615480,12976],[-615480,-156488,1460],[12976,1460]],[[0,0,0],[0,0,0],[0,0]],[[60123600,-2949092,43210],[-2949092,-11500,200],[43210,200]],[[0,0,0],[0,0],[0]],[[124584804,-5458064,47909],[-5458064,93698],[47909]],[[0,0,0],[0,0],[0]],[[173377512,-5621848,27526],[-5621848,79572],[27526]],[[0,0,0],[0,0],[0]],[[158540020,-3216948,8749],[-3216948,29858],[8749]],[[0,0,0],[0,0],[0]],[[82355400,-626264,1460],[-626264,5480],[1460]],[[0,0,0],[0,0],[0]],[[2739184,463428,100],[463428,400],[100]],[[0,0],[0]],[[-31758320,420980],[420980]],[[0,0],[0]],[[-25319396,161084],[161084]],[[0,0],[0]],[[-8801760,34468],[34468]],[[0,0],[0]],[[-63756,4020],[4020]],[[0,0],[0]],[[1390280,200],[200]],[[0]],[[693660]],[[0]],[[182728]],[[0]],[[28744]],[[0]],[[2560]],[[0]],[[100]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
