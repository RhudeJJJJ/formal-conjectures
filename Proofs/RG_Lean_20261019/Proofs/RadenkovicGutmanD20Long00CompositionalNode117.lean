/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode112
import Proofs.RadenkovicGutmanD20Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,480],[0,480,1376]],[[0,0,0],[0,0,0],[0,0,0]],[[0,4320,18720],[4320,17568,27328],[18720,27328,4]],[[0,0,0],[0,0,0],[0,0]],[[228096,438912,270816],[438912,586632,70760],[270816,70760]],[[0,0,0],[0,0,0],[0,0]],[[6958116,6586632,1132516],[6586632,2843168,64416],[1132516,64416]],[[0,0,0],[0,0,0],[0,0]],[[81230040,37599640,2276640],[37599640,6192136,23472],[2276640,23472]],[[0,0,0],[0,0,0],[0,0]],[[495422124,116264632,2588368],[116264632,7529744,2976],[2588368,2976]],[[0,0,0],[0,0,0],[0,0]],[[1862790440,225014176,1776736],[225014176,5518496,8],[1776736,8]],[[0,0,0],[0,0],[0]],[[4738570484,292981528,749624],[292981528,2484688],[749624]],[[0,0,0],[0,0],[0]],[[8624884752,266763896,190048],[266763896,671688],[190048]],[[0,0,0],[0,0],[0]],[[11637544536,173146256,26608],[173146256,100176],[26608]],[[0,0,0],[0,0],[0]],[[11907935304,80525408,1600],[80525408,6408],[1600]],[[0,0,0],[0,0],[0]],[[9370978368,26619320,4],[26619320,16],[4]],[[0,0],[0]],[[5714134400,6104680],[6104680]],[[0,0],[0]],[[2704568672,923800],[923800]],[[0,0],[0]],[[989727224,83200],[83200]],[[0,0],[0]],[[277091220,3432],[3432]],[[0,0],[0]],[[58212464,8],[8]],[[0]],[[8880760]],[[0]],[[929688]],[[0]],[[59956]],[[0]],[[1832]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
