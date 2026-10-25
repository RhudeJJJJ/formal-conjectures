/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode093
import Proofs.RadenkovicGutmanD32Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1024]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-9216],[0,-18432,30336],[-9216,30336,64]],[[0,0,0],[0,0,0],[0,0]],[[-82944,-307584,110208],[-307584,582144,101888],[110208,101888]],[[0,0,0],[0,0,0],[0,0]],[[-3827520,774144,926144],[774144,4087552,111616],[926144,111616]],[[0,0,0],[0,0,0],[0,0]],[[-20729088,21621888,2625280],[21621888,10896384,46976],[2625280,46976]],[[0,0,0],[0,0,0],[0,0]],[[21886656,106648832,3840128],[106648832,15331840,7040],[3840128,7040]],[[0,0,0],[0,0,0],[0,0]],[[584279552,273496064,3251712],[273496064,12609536,128],[3251712,128]],[[0,0,0],[0,0],[0]],[[2669044416,438528000,1649152],[438528000,6250496],[1649152]],[[0,0,0],[0,0],[0]],[[6931122688,473156224,494848],[473156224,1842176],[494848]],[[0,0,0],[0,0],[0]],[[12129141120,355404160,81792],[355404160,300544],[81792]],[[0,0,0],[0,0],[0]],[[15291154944,188238720,6016],[188238720,22016],[6016]],[[0,0,0],[0,0],[0]],[[14361298944,70081408,64],[70081408,256],[64]],[[0,0],[0]],[[10226735616,17974400],[17974400]],[[0,0],[0]],[[5564403712,3036032],[3036032]],[[0,0],[0]],[[2313221632,307712],[307712]],[[0,0],[0]],[[729130176,14976],[14976]],[[0,0],[0]],[[171345408,128],[128]],[[0]],[[29133184]],[[0]],[[3401216]],[[0]],[[247232]],[[0]],[[8960]],[[0]],[[64]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
