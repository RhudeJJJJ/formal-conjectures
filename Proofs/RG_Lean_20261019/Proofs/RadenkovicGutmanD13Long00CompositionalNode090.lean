/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode035
import Proofs.RadenkovicGutmanD13Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-507],[0,-507]],[[0,0,0],[0,0,0],[0,0]],[[0,-4563,-7605],[-4563,-24336,-2275],[-7605,-2275]],[[0,0,0],[0,0,0],[0,0]],[[-82134,-283608,-59007],[-283608,-183300,-3042],[-59007,-3042]],[[0,0,0],[0,0,0],[0,0]],[[-2859948,-2671578,-182702],[-2671578,-551668,-1599],[-182702,-1599]],[[0,0,0],[0,0,0],[0,0]],[[-29642652,-11615812,-296309],[-11615812,-875628,-351],[-296309,-351]],[[0,0,0],[0,0,0],[0,0]],[[-159144336,-29508258,-277238],[-29508258,-808808,-26],[-277238,-26]],[[0,0,0],[0,0],[0]],[[-533167518,-48465482,-154947],[-48465482,-450788],[-154947]],[[0,0,0],[0,0],[0]],[[-1220805092,-54227004,-51558],[-54227004,-151476],[-51558]],[[0,0,0],[0,0],[0]],[[-2012410816,-42483961,-9711],[-42483961,-29380],[-9711]],[[0,0,0],[0,0],[0]],[[-2465622250,-23576397,-897],[-23576397,-2912],[-897]],[[0,0,0],[0,0],[0]],[[-2290222714,-9253205,-26],[-9253205,-104],[-26]],[[0,0],[0]],[[-1631447714,-2528292],[-2528292]],[[0,0],[0]],[[-895781328,-464191],[-464191]],[[0,0],[0]],[[-378801332,-53430],[-53430]],[[0,0],[0]],[[-122510986,-3341],[-3341]],[[0,0],[0]],[[-29868280,-78],[-78]],[[0]],[[-5354336]],[[0]],[[-677170]],[[0]],[[-56264]],[[0]],[[-2678]],[[0]],[[-52]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
