/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode033
import Proofs.RadenkovicGutmanD22Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,484]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,8712],[0,8712]],[[0,0,0],[0,0,0],[0,0]],[[-39204,0,39204],[0,156816,23232],[39204,23232]],[[0,0,0],[0,0,0],[0,0]],[[-679536,705672,209088],[705672,836352,21296],[209088,21296]],[[0,0,0],[0,0,0],[0,0]],[[-2077812,5645376,470448],[5645376,1881792,7744],[470448,7744]],[[0,0,0],[0,0,0],[0,0]],[[9873600,20229264,580800],[20229264,2323200,968],[580800,968]],[[0,0,0],[0,0],[0]],[[94100732,42863040,428824],[42863040,1715296],[428824]],[[0,0,0],[0,0],[0]],[[347368736,59720760,193600],[59720760,774400],[193600]],[[0,0,0],[0,0],[0]],[[793553816,57568896,52272],[57568896,209088],[52272]],[[0,0,0],[0,0],[0]],[[1263729808,39335648,7744],[39335648,30976],[7744]],[[0,0,0],[0,0],[0]],[[1478238608,19189632,484],[19189632,1936],[484]],[[0,0],[0]],[[1304927888,6635640],[6635640]],[[0,0],[0]],[[881437568,1587520],[1587520]],[[0,0],[0]],[[457922080,249744],[249744]],[[0,0],[0]],[[182599164,23232],[23232]],[[0,0],[0]],[[55361856,968],[968]],[[0]],[[12524952]],[[0]],[[2046352]],[[0]],[[227964]],[[0]],[[15488]],[[0]],[[484]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
