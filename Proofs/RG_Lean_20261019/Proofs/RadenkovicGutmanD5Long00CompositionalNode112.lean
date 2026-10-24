/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode110
import Proofs.RadenkovicGutmanD5Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0,0]],[[0,0,225],[0,0,570],[225,570,56]],[[0,0,0],[0,0,0],[0,0,0]],[[2025,5130,5955],[5130,12708,2848],[5955,2848,4]],[[0,0,0],[0,0,0],[0,0]],[[105246,145422,38401],[145422,98472,5020],[38401,5020]],[[0,0,0],[0,0,0],[0,0]],[[1861191,1212822,115206],[1212822,318128,3976],[115206,3976]],[[0,0,0],[0,0,0],[0,0]],[[15606570,5142880,194220],[5142880,566056,1442],[194220,1442]],[[0,0,0],[0,0,0],[0,0]],[[76975369,13309662,199608],[13309662,613704,216],[199608,216]],[[0,0,0],[0,0,0],[0,0]],[[250455660,22935246,129641],[22935246,422016,8],[129641,8]],[[0,0,0],[0,0],[0]],[[574658514,27594668,53614],[27594668,185248],[53614]],[[0,0,0],[0,0],[0]],[[969361522,23801776,13833],[23801776,50728],[13833]],[[0,0,0],[0,0],[0]],[[1235152096,14909286,2093],[14909286,8116],[2093]],[[0,0,0],[0,0],[0]],[[1210005704,6797378,160],[6797378,648],[160]],[[0,0,0],[0,0],[0]],[[921392368,2236990,4],[2236990,16],[4]],[[0,0],[0]],[[548443630,520200],[520200]],[[0,0],[0]],[[255392757,82050],[82050]],[[0,0],[0]],[[92662964,8130],[8130]],[[0,0],[0]],[[25940970,432],[432]],[[0,0],[0]],[[5507814,8],[8]],[[0]],[[862365]],[[0]],[[95098]],[[0]],[[6821]],[[0]],[[272]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
