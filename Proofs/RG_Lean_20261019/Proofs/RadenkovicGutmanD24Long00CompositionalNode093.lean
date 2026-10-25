/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode033
import Proofs.RadenkovicGutmanD24Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,576]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,13824],[0,13824,48]],[[0,0,0],[0,0,0],[0,0]],[[-46656,-31104,77760],[-31104,300672,43488],[77760,43488]],[[0,0,0],[0,0,0],[0,0]],[[-1279152,1181952,470448],[1181952,1791936,46080],[470448,46080]],[[0,0,0],[0,0,0],[0,0]],[[-5495040,11599200,1181952],[11599200,4422528,19392],[1181952,19392]],[[0,0,0],[0,0,0],[0,0]],[[13161744,46406016,1609920],[46406016,5912064,3072],[1609920,3072]],[[0,0,0],[0,0,0],[0,0]],[[189071424,106923456,1300608],[106923456,4690944,96],[1300608,96]],[[0,0,0],[0,0],[0]],[[784491216,160008192,640416],[160008192,2273664],[640416]],[[0,0,0],[0,0],[0]],[[1936352256,164536992,189696],[164536992,665472],[189696]],[[0,0,0],[0,0],[0]],[[3282234144,119486592,31680],[119486592,110592],[31680]],[[0,0,0],[0,0],[0]],[[4055239488,61882368,2496],[61882368,8832],[2496]],[[0,0,0],[0,0],[0]],[[3764303808,22760064,48],[22760064,192],[48]],[[0,0],[0]],[[2667062976,5830560],[5830560]],[[0,0],[0]],[[1451950080,998400],[998400]],[[0,0],[0]],[[607037376,105408],[105408]],[[0,0],[0]],[[193449168,5760],[5760]],[[0,0],[0]],[[46253952,96],[96]],[[0]],[[8073504]],[[0]],[[982272]],[[0]],[[76752]],[[0]],[[3264]],[[0]],[[48]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
