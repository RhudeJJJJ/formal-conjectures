/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode096
import Proofs.RadenkovicGutmanD28Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4704],[0,4704,-1456]],[[0,0,0],[0,0,0],[0,0]],[[0,0,56448],[0,192528,-5656],[56448,-5656]],[[0,0,0],[0,0,0],[0,0]],[[199584,1564920,302232],[1564920,920136,-44072],[302232,-44072]],[[0,0,0],[0,0,0],[0,0]],[[13742568,13676040,615608],[13676040,1478624,-52192],[615608,-52192]],[[0,0,0],[0,0,0],[0,0]],[[148688568,52085376,519120],[52085376,368872,-21336],[519120,-21336]],[[0,0,0],[0,0,0],[0,0]],[[777690480,112919688,-11368],[112919688,-1712144,-2856],[-11368,-2856]],[[0,0,0],[0,0],[0]],[[2483416264,152263440,-362208],[152263440,-2397696],[-362208]],[[0,0,0],[0,0],[0]],[[5348066696,129489304,-290136],[129489304,-1473920],[-290136]],[[0,0,0],[0,0],[0]],[[8175488720,64142512,-106512],[64142512,-482328],[-106512]],[[0,0,0],[0,0],[0]],[[9112656336,10212552,-19320],[10212552,-81760],[-19320]],[[0,0,0],[0,0],[0]],[[7481612264,-8800344,-1400],[-8800344,-5656],[-1400]],[[0,0],[0]],[[4495558144,-7137424],[-7137424]],[[0,0],[0]],[[1913095296,-2561776],[-2561776]],[[0,0],[0]],[[518844592,-521584],[-521584]],[[0,0],[0]],[[49303576,-58352],[-58352]],[[0,0],[0]],[[-25459896,-2800],[-2800]],[[0]],[[-13594000]],[[0]],[[-3330096]],[[0]],[[-479080]],[[0]],[[-39032]],[[0]],[[-1400]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
