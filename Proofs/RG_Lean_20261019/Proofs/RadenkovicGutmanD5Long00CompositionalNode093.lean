/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode033
import Proofs.RadenkovicGutmanD5Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,600],[0,600,10]],[[0,0,0],[0,0,0],[0,0]],[[-2025,-1350,3375],[-1350,13050,2030],[3375,2030]],[[0,0,0],[0,0,0],[0,0]],[[-56160,51300,21060],[51300,80340,2380],[21060,2380]],[[0,0,0],[0,0,0],[0,0]],[[-249615,514980,54720],[514980,205630,1190],[54720,1190]],[[0,0,0],[0,0,0],[0,0]],[[537270,2106490,77570],[2106490,287380,260],[77570,260]],[[0,0,0],[0,0,0],[0,0]],[[8367725,4971660,65950],[4971660,241600,20],[65950,20]],[[0,0,0],[0,0],[0]],[[35588280,7645900,34810],[7645900,126740],[34810]],[[0,0,0],[0,0],[0]],[[89724890,8118200,11400],[8118200,41550],[11400]],[[0,0,0],[0,0],[0]],[[155438040,6127690,2230],[6127690,8220],[2230]],[[0,0,0],[0,0],[0]],[[196679170,3329270,235],[3329270,890],[235]],[[0,0,0],[0,0],[0]],[[187560420,1301730,10],[1301730,40],[10]],[[0,0],[0]],[[137102320,361600],[361600]],[[0,0],[0]],[[77436120,69300],[69300]],[[0,0],[0]],[[33837225,8660],[8660]],[[0,0],[0]],[[11382960,630],[630]],[[0,0],[0]],[[2913090,20],[20]],[[0]],[[555280]],[[0]],[[76105]],[[0]],[[7060]],[[0]],[[395]],[[0]],[[10]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
