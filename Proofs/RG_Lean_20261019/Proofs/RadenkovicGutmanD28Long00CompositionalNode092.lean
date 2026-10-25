/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode089
import Proofs.RadenkovicGutmanD28Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4704],[0,4704,-1456]],[[0,0,0],[0,0,0],[0,0]],[[0,0,56448],[0,190512,-5656],[56448,-5656]],[[0,0,0],[0,0,0],[0,0]],[[181440,1546776,302232],[1546776,903168,-44072],[302232,-44072]],[[0,0,0],[0,0,0],[0,0]],[[13269312,13474944,615608],[13474944,1423632,-52192],[615608,-52192]],[[0,0,0],[0,0,0],[0,0]],[[144090576,51138864,519120],[51138864,281120,-21336],[519120,-21336]],[[0,0,0],[0,0,0],[0,0]],[[753447408,110420688,-11368],[110420688,-1785952,-2856],[-11368,-2856]],[[0,0,0],[0,0],[0]],[[2402891456,148145536,-362208],[148145536,-2428832],[-362208]],[[0,0,0],[0,0],[0]],[[5166063728,125050240,-290136],[125050240,-1478064],[-290136]],[[0,0,0],[0,0],[0]],[[7882919072,60977168,-106512],[60977168,-480928],[-106512]],[[0,0,0],[0,0],[0]],[[8769620048,8762488,-19320],[8762488,-81200],[-19320]],[[0,0,0],[0,0],[0]],[[7184844912,-9175768,-1400],[-9175768,-5600],[-1400]],[[0,0],[0]],[[4306455888,-7156968],[-7156968]],[[0,0],[0]],[[1826154064,-2541056],[-2541056]],[[0,0],[0]],[[491750672,-514472],[-514472]],[[0,0],[0]],[[44760352,-57344],[-57344]],[[0,0],[0]],[[-25166960,-2744],[-2744]],[[0]],[[-13191808]],[[0]],[[-3215184]],[[0]],[[-461328]],[[0]],[[-37520]],[[0]],[[-1344]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
