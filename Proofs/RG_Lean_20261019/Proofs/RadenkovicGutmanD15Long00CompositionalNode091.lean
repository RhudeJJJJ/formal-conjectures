/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,675],[0,675]],[[0,0,0],[0,0,0],[0,0]],[[0,6075,10125],[6075,32400,3015],[10125,3015]],[[0,0,0],[0,0,0],[0,0]],[[109350,377460,78435],[377460,243540,3990],[78435,3990]],[[0,0,0],[0,0,0],[0,0]],[[3805380,3551850,242370],[3551850,730980,2055],[242370,2055]],[[0,0,0],[0,0,0],[0,0]],[[39409740,15423300,392085],[15423300,1156140,435],[392085,435]],[[0,0,0],[0,0,0],[0,0]],[[211384080,39121770,365610],[39121770,1062840,30],[365610,30]],[[0,0,0],[0,0],[0]],[[707436990,64140930,203355],[64140930,588420],[203355]],[[0,0,0],[0,0],[0]],[[1617905340,71611740,67170],[71611740,195780],[67170]],[[0,0,0],[0,0],[0]],[[2663373120,55954425,12495],[55954425,37380],[12495]],[[0,0,0],[0,0],[0]],[[3258049530,30946185,1125],[30946185,3600],[1125]],[[0,0,0],[0,0],[0]],[[3020695170,12091185,30],[12091185,120],[30]],[[0,0],[0]],[[2147083770,3283320],[3283320]],[[0,0],[0]],[[1175780520,597375],[597375]],[[0,0],[0]],[[495585300,67770],[67770]],[[0,0],[0]],[[159623610,4125],[4125]],[[0,0],[0]],[[38709600,90],[90]],[[0]],[[6889680]],[[0]],[[862530]],[[0]],[[70560]],[[0]],[[3270]],[[0]],[[60]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
