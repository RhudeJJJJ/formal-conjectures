/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode289
import Proofs.RadenkovicGutmanD42Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[7056,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[211680,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2914128,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[24399648,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[138847968,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[568473696,7056,0],[7056,0],[0]],[[0,0,0],[0,0],[0]],[[1729305648,155232,0],[155232,0],[0]],[[0,0,0],[0,0],[0]],[[3980444832,1517040,0],[1517040,0],[0]],[[0,0,0],[0,0],[0]],[[6994768032,8678880,0],[8678880,0],[0]],[[0,0,0],[0,0],[0]],[[9400581792,32252976,0],[32252976,0],[0]],[[0,0,0],[0,0],[0]],[[9615147696,81708480,1764],[81708480,3528],[1764]],[[0,0,0],[0,0],[0]],[[7394278752,144125856,24696],[144125856,49392],[24696]],[[0,0,0],[0,0],[0]],[[4184024544,177670080,142884],[177670080,285768],[142884]],[[0,0,0],[0,0],[0]],[[1680696864,151358256,441000],[151358256,882000],[441000]],[[0,0,0],[0,0],[0]],[[450941904,86577120,783216],[86577120,1566432],[783216]],[[0,0,0],[0,0],[0]],[[72013536,31434480,807912],[31434480,1615824],[807912]],[[0,0,0],[0,0],[0]],[[5143824,6477408,467460],[6477408,934920],[467460]],[[0,0,0],[0,0],[0]],[[0,571536,137592],[571536,275184],[137592]],[[0,0,0],[0,0],[0]],[[0,0,15876],[0,31752],[15876]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
