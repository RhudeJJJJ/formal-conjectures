/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[2704],[0],[0]],[[0,0],[0,0],[0]],[[81120,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1116752,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[9350432,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[53209312,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[217850464,2704,0],[2704,0],[0]],[[0,0,0],[0,0],[0]],[[662704432,59488,0],[59488,0],[0]],[[0,0,0],[0,0],[0]],[[1525385888,581360,0],[581360,0],[0]],[[0,0,0],[0,0],[0]],[[2680534688,3325920,0],[3325920,0],[0]],[[0,0,0],[0,0],[0]],[[3602490528,12359984,0],[12359984,0],[0]],[[0,0,0],[0,0],[0]],[[3684716464,31312320,676],[31312320,1352],[676]],[[0,0,0],[0,0],[0]],[[2833635168,55231904,9464],[55231904,18928],[9464]],[[0,0,0],[0,0],[0]],[[1603401696,68086720,54756],[68086720,109512],[54756]],[[0,0,0],[0,0],[0]],[[644076576,58003504,169000],[58003504,338000],[169000]],[[0,0,0],[0,0],[0]],[[172809936,33178080,300144],[33178080,600288],[300144]],[[0,0,0],[0,0],[0]],[[27597024,12046320,309608],[12046320,619216],[309608]],[[0,0,0],[0,0],[0]],[[1971216,2482272,179140],[2482272,358280],[179140]],[[0,0,0],[0,0],[0]],[[0,219024,52728],[219024,105456],[52728]],[[0,0,0],[0,0],[0]],[[0,0,6084],[0,12168],[6084]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
