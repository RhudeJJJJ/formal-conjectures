/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode043
import Proofs.RadenkovicGutmanD30Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2700],[0,2700,-1680]],[[0,0,0],[0,0,0],[0,0]],[[0,24300,24300],[24300,99360,-18540],[24300,-18540]],[[0,0,0],[0,0,0],[0,0]],[[592920,991440,34020],[991440,154800,-66240],[34020,-66240]],[[0,0,0],[0,0,0],[0,0]],[[13659840,5870880,-255960],[5870880,-960240,-67620],[-255960,-67620]],[[0,0,0],[0,0,0],[0,0]],[[108689040,13526280,-951660],[13526280,-3696720,-25980],[-951660,-25980]],[[0,0,0],[0,0,0],[0,0]],[[461243520,7630920,-1443600],[7630920,-5667840,-3360],[-1443600,-3360]],[[0,0,0],[0,0],[0]],[[1214697720,-29757360,-1201380],[-29757360,-4745520],[-1201380]],[[0,0,0],[0,0],[0]],[[2107581600,-82875000,-587400],[-82875000,-2330160],[-587400]],[[0,0,0],[0,0],[0]],[[2407362240,-108634380,-167940],[-108634380,-668400],[-167940]],[[0,0,0],[0,0],[0]],[[1614540360,-89264460,-25980],[-89264460,-103680],[-25980]],[[0,0,0],[0,0],[0]],[[169366440,-49375500,-1680],[-49375500,-6720],[-1680]],[[0,0],[0]],[[-937266600,-18714600],[-18714600]],[[0,0],[0]],[[-1185158400,-4802700],[-4802700]],[[0,0],[0]],[[-838605360,-798600],[-798600]],[[0,0],[0]],[[-405118680,-77700],[-77700]],[[0,0],[0]],[[-140197680,-3360],[-3360]],[[0]],[[-34948800]],[[0]],[[-6149400]],[[0]],[[-726240]],[[0]],[[-51720]],[[0]],[[-1680]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
