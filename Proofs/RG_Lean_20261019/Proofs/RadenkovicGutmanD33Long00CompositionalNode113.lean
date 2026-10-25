/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-19602,19602],[0,19602]],[[0,0,0],[0,0,0],[0,0]],[[88209,-176418,88209],[-176418,182952,52272],[88209,52272]],[[0,0,0],[0,0,0],[0,0]],[[-58806,-411642,470448],[-411642,1304622,47916],[470448,47916]],[[0,0,0],[0,0,0],[0,0]],[[-3263733,2999106,1058508],[2999106,3236508,17424],[1058508,17424]],[[0,0,0],[0,0,0],[0,0]],[[-8984250,18791784,1306800],[18791784,4260168,2178],[1306800,2178]],[[0,0,0],[0,0],[0]],[[18910485,49721562,964854],[49721562,3314916],[964854]],[[0,0,0],[0,0],[0]],[[179427996,79529670,435600],[79529670,1565982],[435600]],[[0,0,0],[0,0],[0]],[[560588886,85042188,117612],[85042188,439956],[117612]],[[0,0,0],[0,0],[0]],[[1077907446,63283968,17424],[63283968,67518],[17424]],[[0,0,0],[0,0],[0]],[[1450748376,33221034,1089],[33221034,4356],[1089]],[[0,0],[0]],[[1438603848,12251250],[12251250]],[[0,0],[0]],[[1076446008,3103650],[3103650]],[[0,0],[0]],[[613814850,514008],[514008]],[[0,0],[0]],[[266845293,50094],[50094]],[[0,0],[0]],[[87734196,2178],[2178]],[[0]],[[21429342]],[[0]],[[3765762]],[[0]],[[449757]],[[0]],[[32670]],[[0]],[[1089]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
