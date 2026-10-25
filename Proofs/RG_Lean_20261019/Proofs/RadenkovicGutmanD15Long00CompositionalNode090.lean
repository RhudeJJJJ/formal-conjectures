/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode035
import Proofs.RadenkovicGutmanD15Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-675],[0,-675]],[[0,0,0],[0,0,0],[0,0]],[[0,-6075,-10125],[-6075,-32400,-3015],[-10125,-3015]],[[0,0,0],[0,0,0],[0,0]],[[-109350,-377460,-78435],[-377460,-243540,-3990],[-78435,-3990]],[[0,0,0],[0,0,0],[0,0]],[[-3805380,-3551850,-242370],[-3551850,-730980,-2055],[-242370,-2055]],[[0,0,0],[0,0,0],[0,0]],[[-39409740,-15423300,-392085],[-15423300,-1156140,-435],[-392085,-435]],[[0,0,0],[0,0,0],[0,0]],[[-211384080,-39121770,-365610],[-39121770,-1062840,-30],[-365610,-30]],[[0,0,0],[0,0],[0]],[[-707436990,-64140930,-203355],[-64140930,-588420],[-203355]],[[0,0,0],[0,0],[0]],[[-1617905340,-71611740,-67170],[-71611740,-195780],[-67170]],[[0,0,0],[0,0],[0]],[[-2663373120,-55954425,-12495],[-55954425,-37380],[-12495]],[[0,0,0],[0,0],[0]],[[-3258049530,-30946185,-1125],[-30946185,-3600],[-1125]],[[0,0,0],[0,0],[0]],[[-3020695170,-12091185,-30],[-12091185,-120],[-30]],[[0,0],[0]],[[-2147083770,-3283320],[-3283320]],[[0,0],[0]],[[-1175780520,-597375],[-597375]],[[0,0],[0]],[[-495585300,-67770],[-67770]],[[0,0],[0]],[[-159623610,-4125],[-4125]],[[0,0],[0]],[[-38709600,-90],[-90]],[[0]],[[-6889680]],[[0]],[[-862530]],[[0]],[[-70560]],[[0]],[[-3270]],[[0]],[[-60]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
