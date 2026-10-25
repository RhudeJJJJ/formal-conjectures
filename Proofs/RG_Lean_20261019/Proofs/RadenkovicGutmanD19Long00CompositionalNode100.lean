/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode043
import Proofs.RadenkovicGutmanD19Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-3249],[0,-6498,1938],[-3249,1938]],[[0,0,0],[0,0,0],[0,0]],[[0,-128763,-10716],[-128763,7638,8398],[-10716,8398]],[[0,0,0],[0,0,0],[0,0]],[[-1200420,-1060371,26429],[-1060371,246658,10336],[26429,10336]],[[0,0,0],[0,0,0],[0,0]],[[-14589720,-3327147,171874],[-3327147,846982,4522],[171874,4522]],[[0,0,0],[0,0,0],[0,0]],[[-78611094,-4227956,328738],[-4227956,1339652,646],[328738,646]],[[0,0,0],[0,0],[0]],[[-247767030,1778609,320606],[1778609,1176100],[320606]],[[0,0,0],[0,0],[0]],[[-504552942,14426833,176833],[14426833,604314],[176833]],[[0,0,0],[0,0],[0]],[[-684562552,23971312,55670],[23971312,180462],[55670]],[[0,0,0],[0,0],[0]],[[-597182958,22639963,9329],[22639963,28994],[9329]],[[0,0,0],[0,0],[0]],[[-260841044,13875073,646],[13875073,1938],[646]],[[0,0],[0]],[[85899608,5711666],[5711666]],[[0,0],[0]],[[240490790,1571395],[1571395]],[[0,0],[0]],[[208093510,277533],[277533]],[[0,0],[0]],[[112564626,28481],[28481]],[[0,0],[0]],[[42227994,1292],[1292]],[[0]],[[11223300]],[[0]],[[2084110]],[[0]],[[257944]],[[0]],[[19152]],[[0]],[[646]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
