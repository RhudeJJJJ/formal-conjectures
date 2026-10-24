/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode033
import Proofs.RadenkovicGutmanD5Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,75],[0,75,-30]],[[0,0,0],[0,0,0],[0,0]],[[0,-675,675],[-675,2475,-215],[675,-215]],[[0,0,0],[0,0,0],[0,0]],[[-7695,7425,2295],[7425,7230,-1040],[2295,-1040]],[[0,0,0],[0,0,0],[0,0]],[[-22005,60660,90],[60660,-6265,-1145],[90,-1145]],[[0,0,0],[0,0,0],[0,0]],[[163890,122555,-10235],[122555,-52390,-455],[-10235,-455]],[[0,0,0],[0,0,0],[0,0]],[[1039575,-84030,-20100],[-84030,-91500,-60],[-20100,-60]],[[0,0,0],[0,0],[0]],[[2018035,-819025,-18605],[-819025,-80670],[-18605]],[[0,0,0],[0,0],[0]],[[-751870,-1746350,-9650],[-1746350,-40625],[-9650]],[[0,0,0],[0,0],[0]],[[-12303720,-2115095,-2865],[-2115095,-11810],[-2865]],[[0,0,0],[0,0],[0]],[[-31223485,-1675485,-455],[-1675485,-1845],[-455]],[[0,0,0],[0,0],[0]],[[-46818860,-908190,-30],[-908190,-120],[-30]],[[0,0],[0]],[[-48577860,-340050],[-340050]],[[0,0],[0]],[[-36848760,-86600],[-86600]],[[0,0],[0]],[[-20911475,-14330],[-14330]],[[0,0],[0]],[[-8942805,-1390],[-1390]],[[0,0],[0]],[[-2870370,-60],[-60]],[[0]],[[-680940]],[[0]],[[-115815]],[[0]],[[-13355]],[[0]],[[-935]],[[0]],[[-30]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
