/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode051
import Proofs.RadenkovicGutmanD14Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,196]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,4704],[0,4704,28]],[[0,0,0],[0,0,0],[0,0]],[[-15876,10584,26460],[10584,106344,15008],[26460,15008]],[[0,0,0],[0,0,0],[0,0]],[[-82404,713664,161028],[713664,648480,16240],[161028,16240]],[[0,0,0],[0,0,0],[0,0]],[[3938004,5906376,407232],[5906376,1643768,7112],[407232,7112]],[[0,0,0],[0,0,0],[0,0]],[[47054868,22728776,559160],[22728776,2262288,1232],[559160,1232]],[[0,0,0],[0,0,0],[0,0]],[[248994452,51839760,456568],[51839760,1851136,56],[456568,56]],[[0,0,0],[0,0],[0]],[[798623868,77464352,228256],[77464352,927024],[228256]],[[0,0,0],[0,0],[0]],[[1740449032,79737784,69216],[79737784,281400],[69216]],[[0,0,0],[0,0],[0]],[[2731512280,57987384,12040],[57987384,48944],[12040]],[[0,0,0],[0,0],[0]],[[3192589624,30074408,1036],[30074408,4200],[1036]],[[0,0,0],[0,0],[0]],[[2835064736,11081448,28],[11081448,112],[28]],[[0,0],[0]],[[1934200240,2847880],[2847880]],[[0,0],[0]],[[1018276000,490784],[490784]],[[0,0],[0]],[[412976676,52528],[52528]],[[0,0],[0]],[[127981532,2968],[2968]],[[0,0],[0]],[[29820168,56],[56]],[[0]],[[5081720]],[[0]],[[604660]],[[0]],[[46284]],[[0]],[[1932]],[[0]],[[28]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
