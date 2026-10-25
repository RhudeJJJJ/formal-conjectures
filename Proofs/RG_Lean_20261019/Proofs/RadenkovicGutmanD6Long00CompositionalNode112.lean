/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode110
import Proofs.RadenkovicGutmanD6Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0,0]],[[0,0,324],[0,0,792],[324,792,88]],[[0,0,0],[0,0,0],[0,0,0]],[[2916,7128,8316],[7128,17136,4080],[8316,4080,4]],[[0,0,0],[0,0,0],[0,0]],[[145152,197640,53820],[197640,134760,7272],[53820,7272]],[[0,0,0],[0,0,0],[0,0]],[[2519856,1647216,162108],[1647216,438944,5744],[162108,5744]],[[0,0,0],[0,0,0],[0,0]],[[20996712,6994776,273792],[6994776,784200,2040],[273792,2040]],[[0,0,0],[0,0,0],[0,0]],[[103306656,18123696,281184],[18123696,850864,288],[281184,288]],[[0,0,0],[0,0,0],[0,0]],[[335747776,31246136,181924],[31246136,583584,8],[181924,8]],[[0,0,0],[0,0],[0]],[[769815884,37581208,74624],[37581208,254416],[74624]],[[0,0,0],[0,0],[0]],[[1297744040,32373480,18964],[32373480,68744],[18964]],[[0,0,0],[0,0],[0]],[[1652349176,20228232,2788],[20228232,10720],[2788]],[[0,0,0],[0,0],[0]],[[1617127592,9185160,200],[9185160,808],[200]],[[0,0,0],[0,0],[0]],[[1229767008,3003952,4],[3003952,16],[4]],[[0,0],[0]],[[730662360,691832],[691832]],[[0,0],[0]],[[339393972,107440],[107440]],[[0,0],[0]],[[122715888,10360],[10360]],[[0,0],[0]],[[34189324,520],[520]],[[0,0],[0]],[[7209624,8],[8]],[[0]],[[1117516]],[[0]],[[121320]],[[0]],[[8472]],[[0]],[[320]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
