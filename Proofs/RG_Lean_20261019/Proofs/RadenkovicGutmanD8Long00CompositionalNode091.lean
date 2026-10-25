/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,192],[0,192]],[[0,0,0],[0,0,0],[0,0]],[[0,1728,2880],[1728,9216,880],[2880,880]],[[0,0,0],[0,0,0],[0,0]],[[31104,107568,22512],[107568,70080,1232],[22512,1232]],[[0,0,0],[0,0,0],[0,0]],[[1086048,1018368,70352],[1018368,213568,704],[70352,704]],[[0,0,0],[0,0,0],[0,0]],[[11299392,4454272,115424],[4454272,344448,176],[115424,176]],[[0,0,0],[0,0,0],[0,0]],[[60926976,11393888,109648],[11393888,324928,16],[109648,16]],[[0,0,0],[0,0],[0]],[[205111488,18865952,62592],[18865952,186368],[62592]],[[0,0,0],[0,0],[0]],[[472219232,21314304,21488],[21314304,65216],[21488]],[[0,0,0],[0,0],[0]],[[783259136,16898016,4256],[16898016,13440],[4256]],[[0,0,0],[0,0],[0]],[[966504960,9518352,432],[9518352,1472],[432]],[[0,0,0],[0,0],[0]],[[905193824,3808400,16],[3808400,64],[16]],[[0,0],[0]],[[651109024,1067792],[1067792]],[[0,0],[0]],[[361667808,203296],[203296]],[[0,0],[0]],[[155099392,24720],[24720]],[[0,0],[0]],[[51038336,1696],[1696]],[[0,0],[0]],[[12718880,48],[48]],[[0]],[[2346176]],[[0]],[[308480]],[[0]],[[27104]],[[0]],[[1408]],[[0]],[[32]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
