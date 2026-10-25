/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode071
import Proofs.RadenkovicGutmanD26Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-36504,0],[-36504,-7956,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-619164,-692172,0],[-692172,-93756,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12694968,-5573412,0],[-5573412,-449228,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-115317540,-25317812,0],[-25317812,-1135212,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-617670612,-72609212,0],[-72609212,-1654744,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2190361992,-139451468,0],[-139451468,-1444664,0],[0,0]],[[0,0,0],[0,0],[0]],[[-5474224132,-185752476,0],[-185752476,-760604],[0]],[[0,0,0],[0,0],[0]],[[-10021032840,-175242080,0],[-175242080,-235612],[0]],[[0,0,0],[0,0],[0]],[[-13779940460,-118338064,0],[-118338064,-39468],[0]],[[0,0,0],[0,0],[0]],[[-14473240756,-57254652,0],[-57254652,-2756],[0]],[[0,0,0],[0,0],[0]],[[-11732339008,-19648668,0],[-19648668,0],[0]],[[0,0],[0]],[[-7378619768,-4662892],[-4662892]],[[0,0],[0]],[[-3601673660,-726908],[-726908]],[[0,0],[0]],[[-1357958992,-66924],[-66924]],[[0,0],[0]],[[-391102036,-2756],[-2756]],[[0,0],[0]],[[-84351800,0],[0]],[[0]],[[-13175396]],[[0]],[[-1406392]],[[0]],[[-91728]],[[0]],[[-2756]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
