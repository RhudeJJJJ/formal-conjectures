/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode093
import Proofs.RadenkovicGutmanD15Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,225]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-2025],[0,-4050,6570],[-2025,6570,30]],[[0,0,0],[0,0,0],[0,0]],[[-18225,-68445,23355],[-68445,124470,22260],[23355,22260]],[[0,0,0],[0,0,0],[0,0]],[[-857790,135675,198765],[135675,879210,24780],[198765,24780]],[[0,0,0],[0,0,0],[0,0]],[[-4959225,4487265,567090],[4487265,2355210,10800],[567090,10800]],[[0,0,0],[0,0,0],[0,0]],[[1325700,22484280,835140],[22484280,3334260,1770],[835140,1770]],[[0,0,0],[0,0,0],[0,0]],[[112122045,58107645,713340],[58107645,2766060,60],[713340,60]],[[0,0,0],[0,0],[0]],[[538266660,93734595,366315],[93734595,1389210],[366315]],[[0,0,0],[0,0],[0]],[[1424773830,101739000,112110],[101739000,418290],[112110]],[[0,0,0],[0,0],[0]],[[2521444410,76931325,19215],[76931325,71010],[19215]],[[0,0,0],[0,0],[0]],[[3205224720,41080515,1545],[41080515,5730],[1545]],[[0,0,0],[0,0],[0]],[[3031841520,15459150,30],[15459150,120],[30]],[[0,0],[0]],[[2173838370,4025475],[4025475]],[[0,0],[0]],[[1191338910,696135],[696135]],[[0,0],[0]],[[499302405,73605],[73605]],[[0,0],[0]],[[158929980,3960],[3960]],[[0,0],[0]],[[37822410,60],[60]],[[0]],[[6544230]],[[0]],[[784695]],[[0]],[[59790]],[[0]],[[2415]],[[0]],[[30]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
