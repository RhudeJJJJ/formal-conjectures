/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[7744],[0],[0]],[[0,0],[0,0],[0]],[[232320,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3198272,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[26778752,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[152386432,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[623903104,7744,0],[7744,0],[0]],[[0,0,0],[0,0],[0]],[[1897922752,170368,0],[170368,0],[0]],[[0,0,0],[0,0],[0]],[[4368560768,1664960,0],[1664960,0],[0]],[[0,0,0],[0,0],[0]],[[7676797568,9525120,0],[9525120,0],[0]],[[0,0,0],[0,0],[0]],[[10317191808,35397824,0],[35397824,0],[0]],[[0,0,0],[0,0],[0]],[[10552679104,89675520,1936],[89675520,3872],[1936]],[[0,0,0],[0,0],[0]],[[8115262848,158178944,27104],[158178944,54208],[27104]],[[0,0,0],[0,0],[0]],[[4591990656,194993920,156816],[194993920,313632],[156816]],[[0,0,0],[0,0],[0]],[[1844574336,166116544,484000],[166116544,968000],[484000]],[[0,0,0],[0,0],[0]],[[494911296,95018880,859584],[95018880,1719168],[859584]],[[0,0,0],[0,0],[0]],[[79035264,34499520,886688],[34499520,1773376],[886688]],[[0,0,0],[0,0],[0]],[[5645376,7108992,513040],[7108992,1026080],[513040]],[[0,0,0],[0,0],[0]],[[0,627264,151008],[627264,302016],[151008]],[[0,0,0],[0,0],[0]],[[0,0,17424],[0,34848],[17424]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
