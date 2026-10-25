/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[1936],[0],[0]],[[0,0],[0,0],[0]],[[58080,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[799568,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[6694688,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[38096608,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[155975776,1936,0],[1936,0],[0]],[[0,0,0],[0,0],[0]],[[474480688,42592,0],[42592,0],[0]],[[0,0,0],[0,0],[0]],[[1092140192,416240,0],[416240,0],[0]],[[0,0,0],[0,0],[0]],[[1919199392,2381280,0],[2381280,0],[0]],[[0,0,0],[0,0],[0]],[[2579297952,8849456,0],[8849456,0],[0]],[[0,0,0],[0,0],[0]],[[2638169776,22418880,484],[22418880,968],[484]],[[0,0,0],[0,0],[0]],[[2028815712,39544736,6776],[39544736,13552],[6776]],[[0,0,0],[0,0],[0]],[[1147997664,48748480,39204],[48748480,78408],[39204]],[[0,0,0],[0,0],[0]],[[461143584,41529136,121000],[41529136,242000],[121000]],[[0,0,0],[0,0],[0]],[[123727824,23754720,214896],[23754720,429792],[214896]],[[0,0,0],[0,0],[0]],[[19758816,8624880,221672],[8624880,443344],[221672]],[[0,0,0],[0,0],[0]],[[1411344,1777248,128260],[1777248,256520],[128260]],[[0,0,0],[0,0],[0]],[[0,156816,37752],[156816,75504],[37752]],[[0,0,0],[0,0],[0]],[[0,0,4356],[0,8712],[4356]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
