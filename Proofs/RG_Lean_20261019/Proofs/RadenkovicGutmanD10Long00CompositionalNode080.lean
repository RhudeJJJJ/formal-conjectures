/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode035
import Proofs.RadenkovicGutmanD10Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-300],[0,-300]],[[0,0,0],[0,0,0],[0,0]],[[0,-2700,-2700],[-2700,-10800,-1300],[-2700,-1300]],[[0,0,0],[0,0,0],[0,0]],[[-48600,-108000,-18900],[-108000,-75600,-1600],[-18900,-1600]],[[0,0,0],[0,0,0],[0,0]],[[-1198800,-900000,-52200],[-900000,-208800,-700],[-52200,-700]],[[0,0,0],[0,0,0],[0,0]],[[-10713600,-3561400,-75700],[-3561400,-302800,-100],[-75700,-100]],[[0,0,0],[0,0],[0]],[[-52030800,-8322600,-63600],[-8322600,-254400],[-63600]],[[0,0,0],[0,0],[0]],[[-160915800,-12652800,-31900],[-12652800,-127600],[-31900]],[[0,0,0],[0,0],[0]],[[-343894400,-13153000,-9400],[-13153000,-37600],[-9400]],[[0,0,0],[0,0],[0]],[[-532645600,-9587700,-1500],[-9587700,-6000],[-1500]],[[0,0,0],[0,0],[0]],[[-615721400,-4943700,-100],[-4943700,-400],[-100]],[[0,0],[0]],[[-540843400,-1792900],[-1792900]],[[0,0],[0]],[[-364601400,-447000],[-447000]],[[0,0],[0]],[[-189280000,-72900],[-72900]],[[0,0],[0]],[[-75459200,-7000],[-7000]],[[0,0],[0]],[[-22877000,-300],[-300]],[[0]],[[-5175600]],[[0]],[[-845600]],[[0]],[[-94200]],[[0]],[[-6400]],[[0]],[[-200]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
