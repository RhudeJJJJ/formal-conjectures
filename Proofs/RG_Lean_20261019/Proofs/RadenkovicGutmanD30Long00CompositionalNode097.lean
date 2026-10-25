/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode051
import Proofs.RadenkovicGutmanD30Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2700],[0,-2700]],[[0,0,0],[0,0,0],[0,0]],[[0,24300,-40500],[24300,-121500,-11880],[-40500,-11880]],[[0,0,0],[0,0,0],[0,0]],[[364500,-803520,-312120],[-803520,-896940,-15180],[-312120,-15180]],[[0,0,0],[0,0,0],[0,0]],[[-2089800,-9796140,-958140],[-9796140,-2635380,-7260],[-958140,-7260]],[[0,0,0],[0,0,0],[0,0]],[[-61632900,-46054620,-1537020],[-46054620,-4071180,-1320],[-1537020,-1320]],[[0,0,0],[0,0,0],[0,0]],[[-429024060,-121294140,-1417020],[-121294140,-3642600,-60],[-1417020,-60]],[[0,0,0],[0,0],[0]],[[-1626103800,-203118660,-775260],[-203118660,-1949400],[-775260]],[[0,0,0],[0,0],[0]],[[-4004803740,-229583820,-249540],[-229583820,-618660],[-249540]],[[0,0,0],[0,0],[0]],[[-6926582760,-180441900,-44340],[-180441900,-109500],[-44340]],[[0,0,0],[0,0],[0]],[[-8774956620,-99769560,-3600],[-99769560,-9060],[-3600]],[[0,0,0],[0,0],[0]],[[-8343940260,-38692620,-60],[-38692620,-180],[-60]],[[0,0],[0]],[[-6037223040,-10325280],[-10325280]],[[0,0],[0]],[[-3343424400,-1816200],[-1816200]],[[0,0],[0]],[[-1415922660,-192840],[-192840]],[[0,0],[0]],[[-454901760,-10080],[-10080]],[[0,0],[0]],[[-109032300,-120],[-120]],[[0]],[[-18930600]],[[0]],[[-2262900]],[[0]],[[-169560]],[[0]],[[-6480]],[[0]],[[-60]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
