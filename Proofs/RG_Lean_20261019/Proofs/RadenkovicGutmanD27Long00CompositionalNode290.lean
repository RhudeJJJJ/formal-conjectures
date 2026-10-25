/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode289
import Proofs.RadenkovicGutmanD27Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[2916,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[87480,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1204308,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[10083528,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[57381048,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[234930456,2916,0],[2916,0],[0]],[[0,0,0],[0,0],[0]],[[714662028,64152,0],[64152,0],[0]],[[0,0,0],[0,0],[0]],[[1644979752,626940,0],[626940,0],[0]],[[0,0,0],[0,0],[0]],[[2890694952,3586680,0],[3586680,0],[0]],[[0,0,0],[0,0],[0]],[[3884934312,13329036,0],[13329036,0],[0]],[[0,0,0],[0,0],[0]],[[3973606956,33767280,729],[33767280,1458],[729]],[[0,0,0],[0,0],[0]],[[3055798872,59562216,10206],[59562216,20412],[10206]],[[0,0,0],[0,0],[0]],[[1729112184,73424880,59049],[73424880,118098],[59049]],[[0,0,0],[0,0],[0]],[[694573704,62551116,182250],[62551116,364500],[182250]],[[0,0,0],[0,0],[0]],[[186358644,35779320,323676],[35779320,647352],[323676]],[[0,0,0],[0,0],[0]],[[29760696,12990780,333882],[12990780,667764],[333882]],[[0,0,0],[0,0],[0]],[[2125764,2676888,193185],[2676888,386370],[193185]],[[0,0,0],[0,0],[0]],[[0,236196,56862],[236196,113724],[56862]],[[0,0,0],[0,0],[0]],[[0,0,6561],[0,13122],[6561]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
