/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode035
import Proofs.RadenkovicGutmanD30Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2700],[0,-2700]],[[0,0,0],[0,0,0],[0,0]],[[0,-24300,-24300],[-24300,-97200,-11700],[-24300,-11700]],[[0,0,0],[0,0,0],[0,0]],[[-437400,-972000,-170100],[-972000,-680400,-14400],[-170100,-14400]],[[0,0,0],[0,0,0],[0,0]],[[-10789200,-8100000,-469800],[-8100000,-1879200,-6300],[-469800,-6300]],[[0,0,0],[0,0,0],[0,0]],[[-96422400,-32052600,-681300],[-32052600,-2725200,-900],[-681300,-900]],[[0,0,0],[0,0],[0]],[[-468277200,-74903400,-572400],[-74903400,-2289600],[-572400]],[[0,0,0],[0,0],[0]],[[-1448242200,-113875200,-287100],[-113875200,-1148400],[-287100]],[[0,0,0],[0,0],[0]],[[-3095049600,-118377000,-84600],[-118377000,-338400],[-84600]],[[0,0,0],[0,0],[0]],[[-4793810400,-86289300,-13500],[-86289300,-54000],[-13500]],[[0,0,0],[0,0],[0]],[[-5541492600,-44493300,-900],[-44493300,-3600],[-900]],[[0,0],[0]],[[-4867590600,-16136100],[-16136100]],[[0,0],[0]],[[-3281412600,-4023000],[-4023000]],[[0,0],[0]],[[-1703520000,-656100],[-656100]],[[0,0],[0]],[[-679132800,-63000],[-63000]],[[0,0],[0]],[[-205893000,-2700],[-2700]],[[0]],[[-46580400]],[[0]],[[-7610400]],[[0]],[[-847800]],[[0]],[[-57600]],[[0]],[[-1800]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
