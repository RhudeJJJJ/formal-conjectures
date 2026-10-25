/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode089
import Proofs.RadenkovicGutmanD25Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3750],[0,3750,-1150]],[[0,0,0],[0,0,0],[0,0]],[[0,0,45000],[0,151875,-4300],[45000,-4300]],[[0,0,0],[0,0,0],[0,0]],[[143775,1233225,241950],[1233225,724050,-34550],[241950,-34550]],[[0,0,0],[0,0,0],[0,0]],[[10565775,10763550,496400],[10763550,1157475,-41050],[496400,-41050]],[[0,0,0],[0,0,0],[0,0]],[[114886350,40940775,427050],[40940775,276950,-16800],[427050,-16800]],[[0,0,0],[0,0,0],[0,0]],[[601436175,88665300,7850],[88665300,-1356100,-2250],[7850,-2250]],[[0,0,0],[0,0],[0]],[[1920440825,119495425,-275850],[119495425,-1884650],[-275850]],[[0,0,0],[0,0],[0]],[[4134664550,101689150,-225300],[101689150,-1154325],[-225300]],[[0,0,0],[0,0],[0]],[[6320204600,50589650,-83250],[50589650,-376750],[-83250]],[[0,0,0],[0,0],[0]],[[7047597125,8369800,-15150],[8369800,-63725],[-15150]],[[0,0,0],[0,0],[0]],[[5793423150,-6625225,-1100],[-6625225,-4400],[-1100]],[[0,0],[0]],[[3490941150,-5462550],[-5462550]],[[0,0],[0]],[[1494843400,-1966625],[-1966625]],[[0,0],[0]],[[412297625,-400700],[-400700]],[[0,0],[0]],[[43767325,-44825],[-44825]],[[0,0],[0]],[[-17611850,-2150],[-2150]],[[0]],[[-9961900]],[[0]],[[-2472525]],[[0]],[[-357675]],[[0]],[[-29225]],[[0]],[[-1050]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
