/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode111
import Proofs.RadenkovicGutmanD4Long00CompositionalNode115
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e116 : NestedArithmetic.Expr 3 := .plus e111 e115
noncomputable def p116 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,96],[0,96,32]],[[0,0,0],[0,0,0],[0,0,0]],[[0,864,1440],[864,3744,1088],[1440,1088,4]],[[0,0,0],[0,0,0],[0,0]],[[25920,48384,14496],[48384,40584,2536],[14496,2536]],[[0,0,0],[0,0,0],[0,0]],[[695844,516744,53860],[516744,156704,2336],[53860,2336]],[[0,0,0],[0,0,0],[0,0]],[[7055640,2526872,103072],[2526872,311816,944],[103072,944]],[[0,0,0],[0,0,0],[0,0]],[[39041196,7185848,115280],[7185848,365328,160],[115280,160]],[[0,0,0],[0,0,0],[0,0]],[[137411432,13243552,79712],[13243552,266400,8],[79712,8]],[[0,0,0],[0,0],[0]],[[333902836,16760984,34744],[16760984,122832],[34744]],[[0,0,0],[0,0],[0]],[[588463248,15046392,9440],[15046392,35272],[9440]],[[0,0,0],[0,0],[0]],[[776221272,9742736,1520],[9742736,5968],[1520]],[[0,0,0],[0,0],[0]],[[782165832,4573536,128],[4573536,520],[128]],[[0,0,0],[0,0],[0]],[[609878848,1547448,4],[1547448,16],[4]],[[0,0],[0]],[[370568832,370408],[370408]],[[0,0],[0]],[[175801184,60440],[60440]],[[0,0],[0]],[[64918584,6272],[6272]],[[0,0],[0]],[[18497684,360],[360]],[[0,0],[0]],[[4002544,8],[8]],[[0]],[[640632]],[[0]],[[72664]],[[0]],[[5428]],[[0]],[[232]],[[0]],[[4]]]
theorem step116 : p116=NestedHorner.add p111 p115 := by decide +kernel
#print axioms step116
theorem h116 : NestedArithmetic.compile e116=p116 := StagedExprCompile.compile_plus e116 e111 e115 p111 p115 p116 rfl h111 h115 step116
#print axioms h116
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
