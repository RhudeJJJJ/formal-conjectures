/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode113
import Proofs.RadenkovicGutmanD13Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0]],[[0,0,1521],[0,0,3042],[1521,3042]],[[0,0,0],[0,0,0],[0,0]],[[13689,27378,26871],[27378,54756,8112],[26871,8112]],[[0,0,0],[0,0,0],[0,0]],[[483678,556686,117793],[556686,292032,7436],[117793,7436]],[[0,0,0],[0,0,0],[0,0]],[[6392763,3477006,241670],[3477006,657072,2704],[241670,2704]],[[0,0,0],[0,0,0],[0,0]],[[41808234,11210784,277836],[11210784,811200,338],[277836,338]],[[0,0,0],[0,0],[0]],[[163953829,22217078,191984],[22217078,598936],[191984]],[[0,0,0],[0,0],[0]],[[428695540,29363750,81289],[29363750,270400],[81289]],[[0,0,0],[0,0],[0]],[[795405598,27005524,20618],[27005524,73008],[20618]],[[0,0,0],[0,0],[0]],[[1088457682,17649008,2873],[17649008,10816],[2873]],[[0,0,0],[0,0],[0]],[[1125761728,8245510,169],[8245510,676],[169]],[[0,0],[0]],[[893388080,2732730],[2732730]],[[0,0],[0]],[[548398240,626990],[626990]],[[0,0],[0]],[[260932958,94640],[94640]],[[0,0],[0]],[[95873869,8450],[8450]],[[0,0],[0]],[[26917644,338],[338]],[[0]],[[5663190]],[[0]],[[863590]],[[0]],[[90077]],[[0]],[[5746]],[[0]],[[169]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
