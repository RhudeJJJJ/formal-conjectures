/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode089
import Proofs.RadenkovicGutmanD32Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6144],[0,6144,-1920]],[[0,0,0],[0,0,0],[0,0]],[[0,0,73728],[0,248832,-7744],[73728,-7744]],[[0,0,0],[0,0,0],[0,0]],[[238464,2020032,393024],[2020032,1172736,-58560],[393024,-58560]],[[0,0,0],[0,0,0],[0,0]],[[17352576,17563392,794432],[17563392,1820928,-69120],[794432,-69120]],[[0,0,0],[0,0,0],[0,0]],[[188168832,66498048,655488],[66498048,276992,-28224],[655488,-28224]],[[0,0,0],[0,0,0],[0,0]],[[982742016,143133056,-43712],[143133056,-2448128,-3776],[-43712,-3776]],[[0,0,0],[0,0],[0]],[[3130158208,191115904,-495104],[191115904,-3260416],[-495104]],[[0,0,0],[0,0],[0]],[[6719675776,159917824,-389184],[159917824,-1971456],[-389184]],[[0,0,0],[0,0],[0]],[[10234635008,76266112,-141952],[76266112,-639488],[-141952]],[[0,0,0],[0,0],[0]],[[11357754368,9082176,-25664],[9082176,-107776],[-25664]],[[0,0,0],[0,0],[0]],[[9272144256,-13161664,-1856],[-13161664,-7424],[-1856]],[[0,0],[0]],[[5526009472,-9762496],[-9762496]],[[0,0],[0]],[[2318544768,-3419776],[-3419776]],[[0,0],[0]],[[607680512,-688064],[-688064]],[[0,0],[0]],[[44664704,-76416],[-76416]],[[0,0],[0]],[[-37054336,-3648],[-3648]],[[0]],[[-18176512]],[[0]],[[-4354048]],[[0]],[[-619776]],[[0]],[[-50176]],[[0]],[[-1792]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
