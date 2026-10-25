/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode033
import Proofs.RadenkovicGutmanD10Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,300],[0,300,-160]],[[0,0,0],[0,0,0],[0,0]],[[0,-2700,2700],[-2700,9900,-1580],[2700,-1580]],[[0,0,0],[0,0,0],[0,0]],[[-27540,29700,5940],[29700,15960,-6080],[5940,-6080]],[[0,0,0],[0,0,0],[0,0]],[[-31860,184320,-16920],[184320,-94180,-6340],[-16920,-6340]],[[0,0,0],[0,0,0],[0,0]],[[827280,23660,-79820],[23660,-365080,-2460],[-79820,-2460]],[[0,0,0],[0,0,0],[0,0]],[[3342300,-2007960,-128400],[-2007960,-558000,-320],[-128400,-320]],[[0,0,0],[0,0],[0]],[[295220,-6818500,-109860],[-6818500,-464440],[-109860]],[[0,0,0],[0,0],[0]],[[-31715640,-11921000,-54600],[-11921000,-226500],[-54600]],[[0,0,0],[0,0],[0]],[[-114797840,-13218140,-15780],[-13218140,-64520],[-15780]],[[0,0,0],[0,0],[0]],[[-229334420,-9952820,-2460],[-9952820,-9940],[-2460]],[[0,0,0],[0,0],[0]],[[-309443920,-5218680,-160],[-5218680,-640],[-160]],[[0,0],[0]],[[-302156720,-1908600],[-1908600]],[[0,0],[0]],[[-220241120,-477600],[-477600]],[[0,0],[0]],[[-121490700,-77960],[-77960]],[[0,0],[0]],[[-50862060,-7480],[-7480]],[[0,0],[0]],[[-16056840,-320],[-320]],[[0]],[[-3758880]],[[0]],[[-632380]],[[0]],[[-72260]],[[0]],[[-5020]],[[0]],[[-160]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
