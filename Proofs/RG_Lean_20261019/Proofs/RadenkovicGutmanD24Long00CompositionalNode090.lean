/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode035
import Proofs.RadenkovicGutmanD24Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1728],[0,-1728]],[[0,0,0],[0,0,0],[0,0]],[[0,-15552,-25920],[-15552,-82944,-7632],[-25920,-7632]],[[0,0,0],[0,0,0],[0,0]],[[-279936,-965520,-200016],[-965520,-620352,-9840],[-200016,-9840]],[[0,0,0],[0,0,0],[0,0]],[[-9727776,-9061632,-615024],[-9061632,-1849536,-4800],[-615024,-4800]],[[0,0,0],[0,0,0],[0,0]],[[-100543680,-39224448,-988704],[-39224448,-2899584,-912],[-988704,-912]],[[0,0,0],[0,0,0],[0,0]],[[-538057728,-99126048,-914160],[-99126048,-2633664,-48],[-914160,-48]],[[0,0,0],[0,0],[0]],[[-1796053824,-161803872,-502272],[-161803872,-1433088],[-502272]],[[0,0,0],[0,0],[0]],[[-4095493920,-179682048,-162768],[-179682048,-464448],[-162768]],[[0,0,0],[0,0],[0]],[[-6719193600,-139455264,-29280],[-139455264,-84864],[-29280]],[[0,0,0],[0,0],[0]],[[-8187204864,-76460976,-2448],[-76460976,-7488],[-2448]],[[0,0,0],[0,0],[0]],[[-7555651872,-29529648,-48],[-29529648,-192],[-48]],[[0,0],[0]],[[-5340771552,-7888944],[-7888944]],[[0,0],[0]],[[-2904992928,-1400544],[-1400544]],[[0,0],[0]],[[-1214185728,-152496],[-152496]],[[0,0],[0]],[[-386904192,-8544],[-8544]],[[0,0],[0]],[[-92508000,-144],[-144]],[[0]],[[-16147008]],[[0]],[[-1964544]],[[0]],[[-153504]],[[0]],[[-6528]],[[0]],[[-96]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
