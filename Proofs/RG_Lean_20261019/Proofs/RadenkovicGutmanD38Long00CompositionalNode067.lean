/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode043
import Proofs.RadenkovicGutmanD38Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,12996],[0,25992,-16416],[12996,-16416,5184]],[[0,0,0],[0,0,0],[0,0]],[[0,437076,-35112],[437076,-346272,22176],[-35112,22176]],[[0,0,0],[0,0,0],[0,0]],[[2943864,1088100,-231644],[1088100,-1523416,161280],[-231644,161280]],[[0,0,0],[0,0,0],[0,0]],[[15554808,-5514372,44456],[-5514372,-572480,189792],[44456,189792]],[[0,0,0],[0,0,0],[0,0]],[[-26148744,-27364152,1537680],[-27364152,5857728,77472],[1537680,77472]],[[0,0,0],[0,0,0],[0,0]],[[-453948816,-36003140,3101608],[-36003140,12643472,10368],[3101608,10368]],[[0,0,0],[0,0],[0]],[[-1785599920,26879620,2964420],[26879620,12163752],[2964420]],[[0,0,0],[0,0],[0]],[[-3858461200,153233552,1579448],[153233552,6452320],[1579448]],[[0,0,0],[0,0],[0]],[[-5144718696,240492444,479236],[240492444,1944296],[479236]],[[0,0,0],[0,0],[0]],[[-4015051640,218129780,77472],[218129780,312048],[77472]],[[0,0,0],[0,0],[0]],[[-894826016,128971512,5184],[128971512,20736],[5184]],[[0,0],[0]],[[1935976840,51356180],[51356180]],[[0,0],[0]],[[2840224232,13696876],[13696876]],[[0,0],[0]],[[2148419136,2349532],[2349532]],[[0,0],[0]],[[1085886768,234576],[234576]],[[0,0],[0]],[[389085024,10368],[10368]],[[0]],[[99776200]],[[0]],[[17978696]],[[0]],[[2167080]],[[0]],[[157104]],[[0]],[[5184]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
