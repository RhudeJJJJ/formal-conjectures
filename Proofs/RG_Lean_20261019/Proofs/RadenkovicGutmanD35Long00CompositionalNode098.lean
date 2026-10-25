/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3675],[0,3675]],[[0,0,0],[0,0,0],[0,0]],[[0,-33075,55125],[-33075,165375,16135],[55125,16135]],[[0,0,0],[0,0,0],[0,0]],[[-496125,1093365,424515],[1093365,1219680,20510],[424515,20510]],[[0,0,0],[0,0,0],[0,0]],[[2839725,13321980,1301930],[13321980,3579135,9695],[1301930,9695]],[[0,0,0],[0,0,0],[0,0]],[[83774250,62591165,2085965],[62591165,5520060,1715],[2085965,1715]],[[0,0,0],[0,0,0],[0,0]],[[582945195,164731280,1919890],[164731280,4928000,70],[1919890,70]],[[0,0,0],[0,0],[0]],[[2208561775,275639245,1047795],[275639245,2628850],[1047795]],[[0,0,0],[0,0],[0]],[[5436734380,311263190,335930],[311263190,830095],[335930]],[[0,0,0],[0,0],[0]],[[9398338320,244360725,59255],[244360725,145600],[59255]],[[0,0,0],[0,0],[0]],[[11899439615,134917195,4725],[134917195,11795],[4725]],[[0,0,0],[0,0],[0]],[[11307534770,52223290,70],[52223290,210],[70]],[[0,0],[0]],[[8175274380,13898010],[13898010]],[[0,0],[0]],[[4523344700,2434250],[2434250]],[[0,0],[0]],[[1913450945,256480],[256480]],[[0,0],[0]],[[613855795,13160],[13160]],[[0,0],[0]],[[146844600,140],[140]],[[0]],[[25424700]],[[0]],[[3025925]],[[0]],[[224945]],[[0]],[[8435]],[[0]],[[70]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
