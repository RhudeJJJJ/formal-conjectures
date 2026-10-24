/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode051
import Proofs.RadenkovicGutmanD5Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-75],[0,-75]],[[0,0,0],[0,0,0],[0,0]],[[0,675,-1125],[675,-3375,-355],[-1125,-355]],[[0,0,0],[0,0,0],[0,0]],[[10125,-22545,-8895],[-22545,-25740,-530],[-8895,-530]],[[0,0,0],[0,0,0],[0,0]],[[-61425,-280440,-28190],[-280440,-78855,-335],[-28190,-335]],[[0,0,0],[0,0,0],[0,0]],[[-1794150,-1346645,-47045],[-1346645,-128280,-95],[-47045,-95]],[[0,0,0],[0,0,0],[0,0]],[[-12634635,-3628940,-45670],[-3628940,-122600,-10],[-45670,-10]],[[0,0,0],[0,0],[0]],[[-48559675,-6233485,-26835],[-6233485,-71650],[-26835]],[[0,0,0],[0,0],[0]],[[-121422040,-7252970,-9590],[-7252970,-25735],[-9590]],[[0,0,0],[0,0],[0]],[[-213483960,-5898525,-2015],[-5898525,-5500],[-2015]],[[0,0,0],[0,0],[0]],[[-275356895,-3400135,-225],[-3400135,-635],[-225]],[[0,0,0],[0,0],[0]],[[-267129710,-1390270,-10],[-1390270,-30],[-10]],[[0,0],[0]],[[-197741340,-398130],[-398130]],[[0,0],[0]],[[-112463900,-77450],[-77450]],[[0,0],[0]],[[-49171985,-9640],[-9640]],[[0,0],[0]],[[-16433335,-680],[-680]],[[0,0],[0]],[[-4143300,-20],[-20]],[[0]],[[-770100]],[[0]],[[-101525]],[[0]],[[-8885]],[[0]],[[-455]],[[0]],[[-10]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
