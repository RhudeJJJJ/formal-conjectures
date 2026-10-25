/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode075
import Proofs.RadenkovicGutmanD42Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0]],[[0,0,15876],[0,31752,31752],[15876,31752]],[[0,0,0],[0,0,0],[0,0]],[[-142884,523908,280476],[523908,846720,84672],[280476,84672]],[[0,0,0],[0,0,0],[0,0]],[[1809864,8430156,1229508],[8430156,3983112,77616],[1229508,77616]],[[0,0,0],[0,0,0],[0,0]],[[51009588,48564684,2522520],[48564684,8474256,28224],[2522520,28224]],[[0,0,0],[0,0,0],[0,0]],[[393100344,149491944,2900016],[149491944,10033632,3528],[2900016,3528]],[[0,0,0],[0,0],[0]],[[1635649596,286267212,2003904],[286267212,7133616],[2003904]],[[0,0,0],[0,0],[0]],[[4385833200,367488828,848484],[367488828,3108168],[848484]],[[0,0,0],[0,0],[0]],[[8230277160,329127120,215208],[329127120,811440],[215208]],[[0,0,0],[0,0],[0]],[[11320325352,209794284,29988],[209794284,116424],[29988]],[[0,0,0],[0,0],[0]],[[11734427880,95709348,1764],[95709348,7056],[1764]],[[0,0],[0]],[[9320729040,31004064],[31004064]],[[0,0],[0]],[[5723350920,6958980],[6958980]],[[0,0],[0]],[[2723506632,1028412],[1028412]],[[0,0],[0]],[[1000715436,89964],[89964]],[[0,0],[0]],[[280962864,3528],[3528]],[[0]],[[59111640]],[[0]],[[9014040]],[[0]],[[940212]],[[0]],[[59976]],[[0]],[[1764]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
