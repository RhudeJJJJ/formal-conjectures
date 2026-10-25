/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode075
import Proofs.RadenkovicGutmanD34Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1156]],[[0,0],[0,0,0],[0,0]],[[0,0,10404],[0,20808,20808],[10404,20808]],[[0,0,0],[0,0,0],[0,0]],[[-93636,343332,183804],[343332,554880,55488],[183804,55488]],[[0,0,0],[0,0,0],[0,0]],[[1186056,5524524,805732],[5524524,2610248,50864],[805732,50864]],[[0,0,0],[0,0,0],[0,0]],[[33428052,31825836,1653080],[31825836,5553424,18496],[1653080,18496]],[[0,0,0],[0,0,0],[0,0]],[[257609976,97966376,1900464],[97966376,6575328,2312],[1900464,2312]],[[0,0,0],[0,0],[0]],[[1071888284,187599148,1313216],[187599148,4674864],[1313216]],[[0,0,0],[0,0],[0]],[[2874162800,240826012,556036],[240826012,2036872],[556036]],[[0,0,0],[0,0],[0]],[[5393537640,215686480,141032],[215686480,531760],[141032]],[[0,0,0],[0,0],[0]],[[7418535208,137484236,19652],[137484236,76296],[19652]],[[0,0,0],[0,0],[0]],[[7689908520,62721092,1156],[62721092,4624],[1156]],[[0,0],[0]],[[6108142160,20317856],[20317856]],[[0,0],[0]],[[3750676680,4560420],[4560420]],[[0,0],[0]],[[1784792328,673948],[673948]],[[0,0],[0]],[[655797644,58956],[58956]],[[0,0],[0]],[[184123056,2312],[2312]],[[0]],[[38737560]],[[0]],[[5907160]],[[0]],[[616148]],[[0]],[[39304]],[[0]],[[1156]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
