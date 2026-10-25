/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode043
import Proofs.RadenkovicGutmanD25Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-5625],[0,-11250,3450],[-5625,3450]],[[0,0,0],[0,0,0],[0,0]],[[0,-222075,-17700],[-222075,16350,14950],[-17700,14950]],[[0,0,0],[0,0,0],[0,0]],[[-2065500,-1804275,51725],[-1804275,448450,18400],[51725,18400]],[[0,0,0],[0,0,0],[0,0]],[[-24948000,-5505075,314050],[-5505075,1523950,8050],[314050,8050]],[[0,0,0],[0,0,0],[0,0]],[[-133381350,-6335900,593050],[-6335900,2400500,1150],[593050,1150]],[[0,0,0],[0,0],[0]],[[-416112750,5320025,575150],[5320025,2102500],[575150]],[[0,0,0],[0,0],[0]],[[-834966150,28295425,316225],[28295425,1078650],[316225]],[[0,0,0],[0,0],[0]],[[-1105306600,44860000,99350],[44860000,321750],[99350]],[[0,0,0],[0,0],[0]],[[-914125950,41579275,16625],[41579275,51650],[16625]],[[0,0,0],[0,0],[0]],[[-317623100,25217425,1150],[25217425,3450],[1150]],[[0,0],[0]],[[262556600,10310450],[10310450]],[[0,0],[0]],[[490601750,2822875],[2822875]],[[0,0],[0]],[[397564150,496725],[496725]],[[0,0],[0]],[[209272650,50825],[50825]],[[0,0],[0]],[[77333250,2300],[2300]],[[0]],[[20356500]],[[0]],[[3754750]],[[0]],[[462400]],[[0]],[[34200]],[[0]],[[1150]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
