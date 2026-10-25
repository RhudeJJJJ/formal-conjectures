/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode035
import Proofs.RadenkovicGutmanD43Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5547],[0,-5547]],[[0,0,0],[0,0,0],[0,0]],[[0,-49923,-49923],[-49923,-199692,-24037],[-49923,-24037]],[[0,0,0],[0,0,0],[0,0]],[[-898614,-1996920,-349461],[-1996920,-1397844,-29584],[-349461,-29584]],[[0,0,0],[0,0,0],[0,0]],[[-22165812,-16641000,-965178],[-16641000,-3860712,-12943],[-965178,-12943]],[[0,0,0],[0,0,0],[0,0]],[[-198094464,-65850286,-1399693],[-65850286,-5598772,-1849],[-1399693,-1849]],[[0,0,0],[0,0],[0]],[[-962049492,-153884874,-1175964],[-153884874,-4703856],[-1175964]],[[0,0,0],[0,0],[0]],[[-2975333142,-233950272,-589831],[-233950272,-2359324],[-589831]],[[0,0,0],[0,0],[0]],[[-6358607456,-243198970,-173806],[-243198970,-695224],[-173806]],[[0,0,0],[0,0],[0]],[[-9848617144,-177276573,-27735],[-177276573,-110940],[-27735]],[[0,0,0],[0,0],[0]],[[-11384688686,-91409013,-1849],[-91409013,-7396],[-1849]],[[0,0],[0]],[[-10000194466,-33150721],[-33150721]],[[0,0],[0]],[[-6741479886,-8265030],[-8265030]],[[0,0],[0]],[[-3499787200,-1347921],[-1347921]],[[0,0],[0]],[[-1395240608,-129430],[-129430]],[[0,0],[0]],[[-422995730,-5547],[-5547]],[[0]],[[-95696844]],[[0]],[[-15635144]],[[0]],[[-1741758]],[[0]],[[-118336]],[[0]],[[-3698]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
