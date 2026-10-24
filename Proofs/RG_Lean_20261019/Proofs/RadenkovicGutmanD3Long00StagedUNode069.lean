/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode042
import Proofs.RadenkovicGutmanD3Long00StagedUNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e069 : NestedArithmetic.Expr 3 := .times e042 e064
noncomputable def p069 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-27],[0,-27,6]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-243,-405],[-243,-1512,9],[-405,9,4]],[[0,0,0],[0,0,0],[0,0]],[[-6804,-18792,-2457],[-18792,-9144,294],[-2457,294]],[[0,0,0],[0,0,0],[0,0]],[[-240084,-175122,-5418],[-175122,-20676,489],[-5418,489]],[[0,0,0],[0,0,0],[0,0]],[[-2533734,-749556,-4365],[-749556,-19384,305],[-4365,305]],[[0,0,0],[0,0,0],[0,0]],[[-13940460,-1871598,1914],[-1871598,160,82],[1914,82]],[[0,0,0],[0,0,0],[0,0]],[[-48056616,-2996082,6561],[-2996082,16812,8],[6561,8]],[[0,0,0],[0,0],[0]],[[-113395604,-3200212,5554],[-3200212,16188],[5554]],[[0,0,0],[0,0],[0]],[[-192473924,-2292097,2425],[-2292097,7600],[2425]],[[0,0,0],[0,0],[0]],[[-242074226,-1057565,591],[-1057565,1984],[591]],[[0,0,0],[0,0],[0]],[[-229519286,-263269,76],[-263269,276],[76]],[[0,0,0],[0,0],[0]],[[-165383666,5212,4],[5212,16],[4]],[[0,0],[0]],[[-90529144,29169],[29169]],[[0,0],[0]],[[-37242284,10694],[10694]],[[0,0],[0]],[[-11198140,1979],[1979]],[[0,0],[0]],[[-2299688,194],[194]],[[0,0],[0]],[[-257316,8],[8]],[[0]],[[8166]],[[0]],[[8446]],[[0]],[[1442]],[[0]],[[118]],[[0]],[[4]]]
theorem step069 : p069=NestedArithmetic.mul p042 p064 := by decide +kernel
#print axioms step069
theorem h069 : NestedArithmetic.compile e069=p069 := StagedExprCompile.compile_times e069 e042 e064 p042 p064 p069 rfl h042 h064 step069
#print axioms h069
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
