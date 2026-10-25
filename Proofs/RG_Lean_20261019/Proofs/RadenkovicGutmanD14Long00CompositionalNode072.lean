/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode051
import Proofs.RadenkovicGutmanD14Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,588],[0,588,-336]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-5292,8820],[-5292,26460,-5432],[8820,-5432,-48]],[[0,0,0],[0,0,0],[0,0]],[[-52164,157248,23016],[157248,14508,-22228],[23016,-22228]],[[0,0,0],[0,0,0],[0,0]],[[602424,924876,-64564],[924876,-527628,-26020],[-64564,-26020]],[[0,0,0],[0,0,0],[0,0]],[[6818580,25148,-355588],[25148,-1904052,-11800],[-355588,-11800]],[[0,0,0],[0,0,0],[0,0]],[[14051820,-12083140,-638660],[-12083140,-3046552,-2084],[-638660,-2084]],[[0,0,0],[0,0,0],[0,0]],[[-66643256,-43573820,-604356],[-43573820,-2717480,-96],[-604356,-96]],[[0,0,0],[0,0],[0]],[[-478674164,-81228628,-332188],[-81228628,-1439132],[-332188]],[[0,0,0],[0,0],[0]],[[-1437397752,-95808948,-107596],[-95808948,-454148],[-107596]],[[0,0,0],[0,0],[0]],[[-2714960212,-76552616,-19632],[-76552616,-81244],[-19632]],[[0,0,0],[0,0],[0]],[[-3592532380,-42564404,-1748],[-42564404,-7116],[-1748]],[[0,0,0],[0,0],[0]],[[-3491505024,-16548672,-48],[-16548672,-192],[-48]],[[0,0],[0]],[[-2552541232,-4438168],[-4438168]],[[0,0],[0]],[[-1419624796,-791672],[-791672]],[[0,0],[0]],[[-602087984,-87136],[-87136]],[[0,0],[0]],[[-193654692,-5032],[-5032]],[[0,0],[0]],[[-46559928,-96],[-96]],[[0]],[[-8149420]],[[0]],[[-992152]],[[0]],[[-77440]],[[0]],[[-3284]],[[0]],[[-48]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
