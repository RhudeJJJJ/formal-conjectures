/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode051
import Proofs.RadenkovicGutmanD25Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,625]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,15000],[0,15000,50]],[[0,0,0],[0,0,0],[0,0]],[[-50625,33750,84375],[33750,338400,47150],[84375,47150]],[[0,0,0],[0,0,0],[0,0]],[[-265950,2269350,510300],[2269350,2049000,49900],[510300,49900]],[[0,0,0],[0,0,0],[0,0]],[[12444975,18704700,1281600],[18704700,5152900,20950],[1281600,20950]],[[0,0,0],[0,0,0],[0,0]],[[148561350,71668700,1744850],[71668700,7025200,3300],[1744850,3300]],[[0,0,0],[0,0,0],[0,0]],[[784268675,162699300,1408750],[162699300,5679400,100],[1408750,100]],[[0,0,0],[0,0],[0]],[[2508519550,241851850,693050],[241851850,2797200],[693050]],[[0,0,0],[0,0],[0]],[[5450246750,247440000,205000],[247440000,828100],[205000]],[[0,0,0],[0,0],[0]],[[8525279600,178631050,34150],[178631050,138000],[34150]],[[0,0,0],[0,0],[0]],[[9927428900,91797850,2675],[91797850,10800],[2675]],[[0,0,0],[0,0],[0]],[[8778690600,33419500,50],[33419500,200],[50]],[[0,0],[0]],[[5960053500,8446000],[8446000]],[[0,0],[0]],[[3119573000,1419250],[1419250]],[[0,0],[0]],[[1256233475,145500],[145500]],[[0,0],[0]],[[385817550,7500],[7500]],[[0,0],[0]],[[88832550,100],[100]],[[0]],[[14888000]],[[0]],[[1727375]],[[0]],[[126650]],[[0]],[[4825]],[[0]],[[50]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
