/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode035
import Proofs.RadenkovicGutmanD30Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2700],[0,-2700]],[[0,0,0],[0,0,0],[0,0]],[[0,-24300,-40500],[-24300,-129600,-11880],[-40500,-11880]],[[0,0,0],[0,0,0],[0,0]],[[-437400,-1508220,-312120],[-1508220,-967680,-15180],[-312120,-15180]],[[0,0,0],[0,0,0],[0,0]],[[-15192360,-14142600,-958140],[-14142600,-2878560,-7260],[-958140,-7260]],[[0,0,0],[0,0,0],[0,0]],[[-156919680,-61153200,-1537020],[-61153200,-4499280,-1320],[-1537020,-1320]],[[0,0,0],[0,0,0],[0,0]],[[-839108160,-154350240,-1417020],[-154350240,-4069680,-60],[-1417020,-60]],[[0,0,0],[0,0],[0]],[[-2798529480,-251570160,-775260],[-251570160,-2201040],[-775260]],[[0,0,0],[0,0],[0]],[[-6375071880,-278855280,-249540],[-278855280,-706560],[-249540]],[[0,0,0],[0,0],[0]],[[-10447155840,-215925900,-44340],[-215925900,-126960],[-44340]],[[0,0,0],[0,0],[0]],[[-12712610760,-118032120,-3600],[-118032120,-10800],[-3600]],[[0,0,0],[0,0],[0]],[[-11713347840,-45398520,-60],[-45398520,-240],[-60]],[[0,0],[0]],[[-8263829040,-12057540],[-12057540]],[[0,0],[0]],[[-4484361240,-2121300],[-2121300]],[[0,0],[0]],[[-1868773200,-227340],[-227340]],[[0,0],[0]],[[-593218920,-12300],[-12300]],[[0,0],[0]],[[-141112200,-180],[-180]],[[0]],[[-24453360]],[[0]],[[-2942760]],[[0]],[[-225720]],[[0]],[[-9240]],[[0]],[[-120]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
