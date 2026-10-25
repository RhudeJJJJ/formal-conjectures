/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode043
import Proofs.RadenkovicGutmanD36Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-11664],[0,-23328,7344],[-11664,7344]],[[0,0,0],[0,0,0],[0,0]],[[0,-458784,-34992],[-458784,40176,31824],[-34992,31824]],[[0,0,0],[0,0,0],[0,0]],[[-4257360,-3678048,119232],[-3678048,972864,39168],[119232,39168]],[[0,0,0],[0,0,0],[0,0]],[[-51107760,-10903248,684288],[-10903248,3275568,17136],[684288,17136]],[[0,0,0],[0,0,0],[0,0]],[[-271125792,-11163888,1277712],[-11163888,5140512,2448],[1277712,2448]],[[0,0,0],[0,0],[0]],[[-837075600,15527376,1232928],[15527376,4492800],[1232928]],[[0,0,0],[0,0],[0]],[[-1654004304,65331072,675936],[65331072,2301696],[675936]],[[0,0,0],[0,0],[0]],[[-2131696800,99760032,211968],[99760032,685872],[211968]],[[0,0,0],[0,0],[0]],[[-1655208864,90999360,35424],[90999360,110016],[35424]],[[0,0,0],[0,0],[0]],[[-389822832,54689472,2448],[54689472,7344],[2448]],[[0,0],[0]],[[772842816,22226112],[22226112]],[[0,0],[0]],[[1166266080,6058800],[6058800]],[[0,0],[0]],[[899210592,1062576],[1062576]],[[0,0],[0]],[[462818448,108432],[108432]],[[0,0],[0]],[[168832944,4896],[4896]],[[0]],[[44068320]],[[0]],[[8079840]],[[0]],[[990576]],[[0]],[[73008]],[[0]],[[2448]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
