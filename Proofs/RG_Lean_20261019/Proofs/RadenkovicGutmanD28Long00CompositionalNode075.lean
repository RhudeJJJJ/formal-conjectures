/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode033
import Proofs.RadenkovicGutmanD28Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,784]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,14112],[0,14112]],[[0,0,0],[0,0,0],[0,0]],[[-63504,0,63504],[0,254016,37632],[63504,37632]],[[0,0,0],[0,0,0],[0,0]],[[-1100736,1143072,338688],[1143072,1354752,34496],[338688,34496]],[[0,0,0],[0,0,0],[0,0]],[[-3365712,9144576,762048],[9144576,3048192,12544],[762048,12544]],[[0,0,0],[0,0,0],[0,0]],[[15993600,32768064,940800],[32768064,3763200,1568],[940800,1568]],[[0,0,0],[0,0],[0]],[[152427632,69431040,694624],[69431040,2778496],[694624]],[[0,0,0],[0,0],[0]],[[562679936,96737760,313600],[96737760,1254400],[313600]],[[0,0,0],[0,0],[0]],[[1285426016,93252096,84672],[93252096,338688],[84672]],[[0,0,0],[0,0],[0]],[[2047033408,63717248,12544],[63717248,50176],[12544]],[[0,0,0],[0,0],[0]],[[2394502208,31084032,784],[31084032,3136],[784]],[[0,0],[0]],[[2113767488,10748640],[10748640]],[[0,0],[0]],[[1427783168,2571520],[2571520]],[[0,0],[0]],[[741758080,404544],[404544]],[[0,0],[0]],[[295780464,37632],[37632]],[[0,0],[0]],[[89677056,1568],[1568]],[[0]],[[20288352]],[[0]],[[3314752]],[[0]],[[369264]],[[0]],[[25088]],[[0]],[[784]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
