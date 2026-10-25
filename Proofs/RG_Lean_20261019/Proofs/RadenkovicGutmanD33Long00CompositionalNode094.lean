/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode035
import Proofs.RadenkovicGutmanD33Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-9801],[0,-19602,6138],[-9801,6138]],[[0,0,0],[0,0,0],[0,0]],[[0,-268191,-29700],[-268191,51084,26598],[-29700,26598]],[[0,0,0],[0,0,0],[0,0]],[[-1651914,-1406889,98109],[-1406889,969606,32736],[98109,32736]],[[0,0,0],[0,0,0],[0,0]],[[-11638242,1134837,569250],[1134837,3274524,14322],[569250,14322]],[[0,0,0],[0,0,0],[0,0]],[[-1263438,26093694,1065306],[26093694,5228256,2046],[1065306,2046]],[[0,0,0],[0,0],[0]],[[266513544,89996049,1029006],[89996049,4660524],[1029006]],[[0,0,0],[0,0],[0]],[[1366336224,166379895,564465],[166379895,2434278],[564465]],[[0,0,0],[0,0],[0]],[[3740639100,195454776,177078],[195454776,738804],[177078]],[[0,0,0],[0,0],[0]],[[6752752842,155153691,29601],[155153691,120582],[29601]],[[0,0,0],[0,0],[0]],[[8679483582,85238901,2046],[85238901,8184],[2046]],[[0,0],[0]],[[8247620172,32472660],[32472660]],[[0,0],[0]],[[5909686002,8421435],[8421435]],[[0,0],[0]],[[3221644998,1418571],[1418571]],[[0,0],[0]],[[1336954740,139953],[139953]],[[0,0],[0]],[[419176032,6138],[6138]],[[0]],[[97581528]],[[0]],[[16340478]],[[0]],[[1859814]],[[0]],[[128766]],[[0]],[[4092]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
