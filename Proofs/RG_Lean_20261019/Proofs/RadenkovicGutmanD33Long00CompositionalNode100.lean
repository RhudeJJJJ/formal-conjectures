/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode043
import Proofs.RadenkovicGutmanD33Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-9801],[0,-19602,6138],[-9801,6138]],[[0,0,0],[0,0,0],[0,0]],[[0,-385803,-29700],[-385803,32670,26598],[-29700,26598]],[[0,0,0],[0,0,0],[0,0]],[[-3581820,-3101571,98109],[-3101571,810018,32736],[98109,32736]],[[0,0,0],[0,0,0],[0,0]],[[-43053120,-9250659,569250],[-9250659,2732334,14322],[569250,14322]],[[0,0,0],[0,0,0],[0,0]],[[-228767814,-9723516,1065306],[-9723516,4291188,2046],[1065306,2046]],[[0,0,0],[0,0],[0]],[[-707850990,12266793,1029006],[12266793,3752100],[1029006]],[[0,0,0],[0,0],[0]],[[-1403257350,53740401,564465],[53740401,1922778],[564465]],[[0,0,0],[0,0],[0]],[[-1819041576,82656288,177078],[82656288,573078],[177078]],[[0,0,0],[0,0],[0]],[[-1432557918,75634779,29601],[75634779,91938],[29601]],[[0,0,0],[0,0],[0]],[[-374226204,45537921,2046],[45537921,6138],[2046]],[[0,0],[0]],[[609748920,18529170],[18529170]],[[0,0],[0]],[[954127350,5055435],[5055435]],[[0,0],[0]],[[742596822,887205],[887205]],[[0,0],[0]],[[383883786,90585],[90585]],[[0,0],[0]],[[140395266,4092],[4092]],[[0]],[[36707220]],[[0]],[[6738270]],[[0]],[[826848]],[[0]],[[60984]],[[0]],[[2046]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
