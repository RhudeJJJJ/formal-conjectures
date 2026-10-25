/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode035
import Proofs.RadenkovicGutmanD36Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3888],[0,-3888]],[[0,0,0],[0,0,0],[0,0]],[[0,-34992,-58320],[-34992,-186624,-17064],[-58320,-17064]],[[0,0,0],[0,0,0],[0,0]],[[-629856,-2171448,-449064],[-2171448,-1391904,-21672],[-449064,-21672]],[[0,0,0],[0,0,0],[0,0]],[[-21870000,-20349792,-1377000],[-20349792,-4134240,-10224],[-1377000,-10224]],[[0,0,0],[0,0,0],[0,0]],[[-225791712,-87931008,-2205792],[-87931008,-6448896,-1800],[-2205792,-1800]],[[0,0,0],[0,0,0],[0,0]],[[-1206772992,-221751504,-2029608],[-221751504,-5816736,-72],[-2029608,-72]],[[0,0,0],[0,0],[0]],[[-4022390016,-361062576,-1107216],[-361062576,-3132864],[-1107216]],[[0,0,0],[0,0],[0]],[[-9156931632,-399729600,-354744],[-399729600,-999072],[-354744]],[[0,0,0],[0,0],[0]],[[-14994383616,-309039264,-62496],[-309039264,-177408],[-62496]],[[0,0,0],[0,0],[0]],[[-18229458528,-168585624,-4968],[-168585624,-14688],[-4968]],[[0,0,0],[0,0],[0]],[[-16778557008,-64661976,-72],[-64661976,-288],[-72]],[[0,0],[0]],[[-11822032368,-17104680],[-17104680]],[[0,0],[0]],[[-6404977584,-2990304],[-2990304]],[[0,0],[0]],[[-2663777088,-316872],[-316872]],[[0,0],[0]],[[-843369120,-16704],[-16704]],[[0,0],[0]],[[-199907280,-216],[-216]],[[0]],[[-34467552]],[[0]],[[-4115808]],[[0]],[[-311472]],[[0]],[[-12384]],[[0]],[[-144]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
