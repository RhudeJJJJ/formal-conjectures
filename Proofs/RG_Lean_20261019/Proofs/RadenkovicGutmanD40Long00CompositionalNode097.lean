/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode051
import Proofs.RadenkovicGutmanD40Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4800],[0,-4800]],[[0,0,0],[0,0,0],[0,0]],[[0,43200,-72000],[43200,-216000,-21040],[-72000,-21040]],[[0,0,0],[0,0,0],[0,0]],[[648000,-1427760,-554160],[-1427760,-1591920,-26640],[-554160,-26640]],[[0,0,0],[0,0,0],[0,0]],[[-3704400,-17388720,-1698320],[-17388720,-4667040,-12480],[-1698320,-12480]],[[0,0,0],[0,0,0],[0,0]],[[-109306800,-81659360,-2718560],[-81659360,-7189040,-2160],[-2718560,-2160]],[[0,0,0],[0,0,0],[0,0]],[[-760414080,-214803120,-2498960],[-214803120,-6407200,-80],[-2498960,-80]],[[0,0,0],[0,0],[0]],[[-2880002800,-359207680,-1361280],[-359207680,-3409600],[-1361280]],[[0,0,0],[0,0],[0]],[[-7087083120,-405346960,-435120],[-405346960,-1072480],[-435120]],[[0,0,0],[0,0],[0]],[[-12246472480,-317949600,-76320],[-317949600,-186800],[-76320]],[[0,0,0],[0,0],[0]],[[-15498776960,-175356080,-6000],[-175356080,-14880],[-6000]],[[0,0,0],[0,0],[0]],[[-14720540080,-67777360,-80],[-67777360,-240],[-80]],[[0,0],[0]],[[-10636710720,-17999840],[-17999840]],[[0,0],[0]],[[-5881174400,-3142400],[-3142400]],[[0,0],[0]],[[-2485705280,-329120],[-329120]],[[0,0],[0]],[[-796563280,-16640],[-16640]],[[0,0],[0]],[[-190268400,-160],[-160]],[[0]],[[-32872800]],[[0]],[[-3899200]],[[0]],[[-288080]],[[0]],[[-10640]],[[0]],[[-80]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
