/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode096
import Proofs.RadenkovicGutmanD31Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5766],[0,5766,-1798]],[[0,0,0],[0,0,0],[0,0]],[[0,0,69192],[0,235755,-7192],[69192,-7192]],[[0,0,0],[0,0,0],[0,0]],[[243567,1915893,369210],[1915893,1120836,-54746],[369210,-54746]],[[0,0,0],[0,0,0],[0,0]],[[16804449,16713216,747596],[16713216,1777943,-64666],[747596,-64666]],[[0,0,0],[0,0,0],[0,0]],[[181689264,63517419,619938],[63517419,376216,-26412],[619938,-26412]],[[0,0,0],[0,0,0],[0,0]],[[949407519,137324730,-34906],[137324730,-2191328,-3534],[-34906,-3534]],[[0,0,0],[0,0],[0]],[[3028494067,184421325,-459978],[184421325,-3006690],[-459978]],[[0,0,0],[0,0],[0]],[[6513660356,155717092,-363072],[155717092,-1836905],[-363072]],[[0,0,0],[0,0],[0]],[[9941897780,75794194,-132618],[75794194,-599292],[-132618]],[[0,0,0],[0,0],[0]],[[11059214133,10629528,-23994],[10629528,-101401],[-23994]],[[0,0,0],[0,0],[0]],[[9054018596,-11686845,-1736],[-11686845,-7006],[-1736]],[[0,0],[0]],[[5416319938,-9052372],[-9052372]],[[0,0],[0]],[[2286277404,-3210949],[-3210949]],[[0,0],[0]],[[607624273,-650194],[-650194]],[[0,0],[0]],[[49870723,-72509],[-72509]],[[0,0],[0]],[[-34212468,-3472],[-3472]],[[0]],[[-17302960]],[[0]],[[-4180629]],[[0]],[[-597649]],[[0]],[[-48515]],[[0]],[[-1736]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
