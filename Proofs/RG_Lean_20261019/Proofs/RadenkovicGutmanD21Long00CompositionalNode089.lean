/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode033
import Proofs.RadenkovicGutmanD21Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1323],[0,1323,-798]],[[0,0,0],[0,0,0],[0,0]],[[0,-11907,11907],[-11907,43659,-8631],[11907,-8631]],[[0,0,0],[0,0,0],[0,0]],[[-113967,130977,18711],[130977,40446,-31248],[18711,-31248]],[[0,0,0],[0,0,0],[0,0]],[[-10773,678132,-114534],[678132,-575001,-32025],[-114534,-32025]],[[0,0,0],[0,0,0],[0,0]],[[4044978,-973413,-441819],[-973413,-1969254,-12327],[-441819,-12327]],[[0,0,0],[0,0,0],[0,0]],[[12854583,-12717054,-677124],[-12717054,-2904300,-1596],[-677124,-1596]],[[0,0,0],[0,0],[0]],[[-16662765,-38252529,-566349],[-38252529,-2375646],[-566349]],[[0,0,0],[0,0],[0]],[[-206181822,-63972846,-277746],[-63972846,-1146705],[-277746]],[[0,0,0],[0,0],[0]],[[-657755112,-69282423,-79569],[-69282423,-324450],[-79569]],[[0,0,0],[0,0],[0]],[[-1252622301,-51401469,-12327],[-51401469,-49749],[-12327]],[[0,0,0],[0,0],[0]],[[-1646856876,-26677854,-798],[-26677854,-3192],[-798]],[[0,0],[0]],[[-1581633732,-9683730],[-9683730]],[[0,0],[0]],[[-1139537784,-2409288],[-2409288]],[[0,0],[0]],[[-623195475,-391482],[-391482]],[[0,0],[0]],[[-259161525,-37422],[-37422]],[[0,0],[0]],[[-81379746,-1596],[-1596]],[[0]],[[-18967788]],[[0]],[[-3179463]],[[0]],[[-362187]],[[0]],[[-25095]],[[0]],[[-798]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
