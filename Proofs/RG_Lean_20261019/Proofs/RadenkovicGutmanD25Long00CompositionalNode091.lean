/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1875],[0,1875]],[[0,0,0],[0,0,0],[0,0]],[[0,16875,28125],[16875,90000,8275],[28125,8275]],[[0,0,0],[0,0,0],[0,0]],[[303750,1047600,216975],[1047600,672900,10650],[216975,10650]],[[0,0,0],[0,0,0],[0,0]],[[10554300,9830250,666950],[9830250,2005300,5175],[666950,5175]],[[0,0,0],[0,0,0],[0,0]],[[109071900,42542500,1071725],[42542500,3141900,975],[1071725,975]],[[0,0,0],[0,0,0],[0,0]],[[583606800,107484450,990350],[107484450,2851400,50],[990350,50]],[[0,0,0],[0,0],[0]],[[1947759150,175395050,543675],[175395050,1549700],[543675]],[[0,0,0],[0,0],[0]],[[4440542900,194703900,175950],[194703900,501300],[175950]],[[0,0,0],[0,0],[0]],[[7283627200,151044625,31575],[151044625,91300],[31575]],[[0,0,0],[0,0],[0]],[[8872589050,82765725,2625],[82765725,8000],[2625]],[[0,0,0],[0,0],[0]],[[8185579450,31938725,50],[31938725,200],[50]],[[0,0],[0]],[[5783840450,8522700],[8522700]],[[0,0],[0]],[[3144523200,1510375],[1510375]],[[0,0],[0]],[[1313532500,163950],[163950]],[[0,0],[0]],[[418245850,9125],[9125]],[[0,0],[0]],[[99901000,150],[150]],[[0]],[[17412800]],[[0]],[[2114050]],[[0]],[[164600]],[[0]],[[6950]],[[0]],[[100]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
