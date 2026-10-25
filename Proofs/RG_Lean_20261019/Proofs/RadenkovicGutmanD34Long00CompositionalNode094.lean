/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode035
import Proofs.RadenkovicGutmanD34Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-10404],[0,-20808,6528],[-10404,6528]],[[0,0,0],[0,0,0],[0,0]],[[0,-284580,-31416],[-284580,54672,28288],[-31416,28288]],[[0,0,0],[0,0,0],[0,0]],[[-1751544,-1488996,104924],[-1488996,1032376,34816],[104924,34816]],[[0,0,0],[0,0,0],[0,0]],[[-12304872,1241748,606424],[1241748,3484592,15232],[606424,15232]],[[0,0,0],[0,0,0],[0,0]],[[-899640,27845864,1133968],[27845864,5562400,2176],[1133968,2176]],[[0,0,0],[0,0],[0]],[[285054912,95875988,1094936],[95875988,4957744],[1094936]],[[0,0,0],[0,0],[0]],[[1457030832,177137756,600508],[177137756,2589304],[600508]],[[0,0,0],[0,0],[0]],[[3984952048,208022064,188360],[208022064,785808],[188360]],[[0,0,0],[0,0],[0]],[[7190162920,165094548,31484],[165094548,128248],[31484]],[[0,0,0],[0,0],[0]],[[9238858216,90686908,2176],[90686908,8704],[2176]],[[0,0],[0]],[[8777338816,34544408],[34544408]],[[0,0],[0]],[[6288301496,8957980],[8957980]],[[0,0],[0]],[[3427655192,1508852],[1508852]],[[0,0],[0]],[[1422319824,148852],[148852]],[[0,0],[0]],[[445908368,6528],[6528]],[[0]],[[103798464]],[[0]],[[17380664]],[[0]],[[1978120]],[[0]],[[136952]],[[0]],[[4352]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
