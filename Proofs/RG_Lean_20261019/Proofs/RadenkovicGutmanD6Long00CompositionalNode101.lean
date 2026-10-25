/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode051
import Proofs.RadenkovicGutmanD6Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,864],[0,864,12]],[[0,0,0],[0,0,0],[0,0]],[[-2916,1944,4860],[1944,19656,2880],[4860,2880]],[[0,0,0],[0,0,0],[0,0]],[[-14580,132192,30132],[132192,122400,3312],[30132,3312]],[[0,0,0],[0,0,0],[0,0]],[[742932,1107432,77760],[1107432,317400,1608],[77760,1608]],[[0,0,0],[0,0,0],[0,0]],[[8902116,4315752,109368],[4315752,448464,336],[109368,336]],[[0,0,0],[0,0,0],[0,0]],[[47430036,9976464,92088],[9976464,379008,24],[92088,24]],[[0,0,0],[0,0],[0]],[[153338412,15129600,48000],[15129600,198000],[48000]],[[0,0,0],[0,0],[0]],[[337068552,15837144,15456],[15837144,63768],[15456]],[[0,0,0],[0,0],[0]],[[533979768,11746488,2952],[11746488,12144],[2952]],[[0,0,0],[0,0],[0]],[[630557976,6239976,300],[6239976,1224],[300]],[[0,0,0],[0,0],[0]],[[566403744,2369928,12],[2369928,48],[12]],[[0,0],[0]],[[391510320,633960],[633960]],[[0,0],[0]],[[209281440,115584],[115584]],[[0,0],[0]],[[86440164,13488],[13488]],[[0,0],[0]],[[27396876,888],[888]],[[0,0],[0]],[[6569352,24],[24]],[[0]],[[1163160]],[[0]],[[146100]],[[0]],[[12156]],[[0]],[[588]],[[0]],[[12]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
