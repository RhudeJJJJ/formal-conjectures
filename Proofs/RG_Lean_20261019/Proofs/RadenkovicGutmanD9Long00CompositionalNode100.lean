/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode043
import Proofs.RadenkovicGutmanD9Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-729],[0,-1458,378],[-729,378]],[[0,0,0],[0,0,0],[0,0]],[[0,-29403,-2916],[-29403,-162,1638],[-2916,1638]],[[0,0,0],[0,0,0],[0,0]],[[-277020,-256851,2349],[-256851,42498,2016],[2349,2016]],[[0,0,0],[0,0,0],[0,0]],[[-3460320,-899667,28674],[-899667,155502,882],[28674,882]],[[0,0,0],[0,0,0],[0,0]],[[-19269414,-1539036,59418],[-1539036,251892,126],[59418,126]],[[0,0,0],[0,0],[0]],[[-63301230,-945351,59886],[-945351,224100],[59886]],[[0,0,0],[0,0],[0]],[[-136350342,1246113,33633],[1246113,116154],[33633]],[[0,0,0],[0,0],[0]],[[-201526632,3363552,10710],[3363552,34902],[10710]],[[0,0,0],[0,0],[0]],[[-205860798,3650283,1809],[3650283,5634],[1809]],[[0,0,0],[0,0],[0]],[[-138909564,2395953,126],[2395953,378],[126]],[[0,0],[0]],[[-49029192,1028466],[1028466]],[[0,0],[0]],[[9416790,291195],[291195]],[[0,0],[0]],[[24316470,52533],[52533]],[[0,0],[0]],[[16623306,5481],[5481]],[[0,0],[0]],[[6940674,252],[252]],[[0]],[[1962900]],[[0]],[[379710]],[[0]],[[48384]],[[0]],[[3672]],[[0]],[[126]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
