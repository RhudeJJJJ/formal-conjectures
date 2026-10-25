/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2028],[0,2028]],[[0,0,0],[0,0,0],[0,0]],[[0,-18252,30420],[-18252,91260,8944],[30420,8944]],[[0,0,0],[0,0,0],[0,0]],[[-273780,603720,234624],[603720,674388,11492],[234624,11492]],[[0,0,0],[0,0,0],[0,0]],[[1572480,7364916,720980],[7364916,1984164,5564],[720980,5564]],[[0,0,0],[0,0,0],[0,0]],[[46361484,34648172,1158092],[34648172,3070548,1040],[1158092,1040]],[[0,0,0],[0,0,0],[0,0]],[[322841532,91321412,1069588],[91321412,2753816,52],[1069588,52]],[[0,0,0],[0,0],[0]],[[1224205216,153056644,586716],[153056644,1478776],[586716]],[[0,0,0],[0,0],[0]],[[3016520260,173171492,189644],[173171492,471796],[189644]],[[0,0,0],[0,0],[0]],[[5220170904,136269276,33956],[136269276,84292],[33956]],[[0,0,0],[0,0],[0]],[[6617265356,75461152,2808],[75461152,7124],[2808]],[[0,0,0],[0,0],[0]],[[6296640428,29324932,52],[29324932,156],[52]],[[0,0],[0]],[[4559619168,7848048],[7848048]],[[0,0],[0]],[[2527582928,1386632],[1386632]],[[0,0],[0]],[[1071702788,148408],[148408]],[[0,0],[0]],[[344841016,7904],[7904]],[[0,0],[0]],[[82822740,104],[104]],[[0]],[[14422200]],[[0]],[[1731860]],[[0]],[[130832]],[[0]],[[5096]],[[0]],[[52]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
