/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,300],[0,300]],[[0,0,0],[0,0,0],[0,0]],[[0,-2700,4500],[-2700,13500,1360],[4500,1360]],[[0,0,0],[0,0,0],[0,0]],[[-40500,89640,35040],[89640,100980,1860],[35040,1860]],[[0,0,0],[0,0,0],[0,0]],[[237600,1101780,108980],[1101780,301860,1020],[108980,1020]],[[0,0,0],[0,0,0],[0,0]],[[6979500,5224940,177740],[5224940,476660,240],[177740,240]],[[0,0,0],[0,0,0],[0,0]],[[48817020,13892580,167540],[13892580,439000,20],[167540,20]],[[0,0,0],[0,0],[0]],[[186102400,23514820,94620],[23514820,244600],[94620]],[[0,0,0],[0,0],[0]],[[461262180,26910340,31980],[26910340,82420],[31980]],[[0,0,0],[0,0],[0]],[[803346520,21467100,6180],[21467100,16100],[6180]],[[0,0,0],[0,0],[0]],[[1025568140,12091520,600],[12091520,1620],[600]],[[0,0,0],[0,0],[0]],[[983670220,4803940,20],[4803940,60],[20]],[[0,0],[0]],[[718867680,1325360],[1325360]],[[0,0],[0]],[[402837200,245000],[245000]],[[0,0],[0]],[[173070020,28280],[28280]],[[0,0],[0]],[[56620120,1760],[1760]],[[0,0],[0]],[[13898100,40],[40]],[[0]],[[2494200]],[[0]],[[313300]],[[0]],[[25520]],[[0]],[[1160]],[[0]],[[20]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
