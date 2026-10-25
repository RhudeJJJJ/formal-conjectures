/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode033
import Proofs.RadenkovicGutmanD6Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,864],[0,864,12]],[[0,0,0],[0,0,0],[0,0]],[[-2916,-1944,4860],[-1944,18792,2880],[4860,2880]],[[0,0,0],[0,0,0],[0,0]],[[-80676,73872,30132],[73872,114912,3312],[30132,3312]],[[0,0,0],[0,0,0],[0,0]],[[-356076,738072,77760],[738072,291960,1608],[77760,1608]],[[0,0,0],[0,0,0],[0,0]],[[783972,3005352,109368],[3005352,404496,336],[109368,336]],[[0,0,0],[0,0,0],[0,0]],[[12000564,7058880,92088],[7058880,336384,24],[92088,24]],[[0,0,0],[0,0],[0]],[[50780508,10797552,48000],[10797552,174000],[48000]],[[0,0,0],[0,0],[0]],[[127481352,11394072,15456],[11394072,55992],[15456]],[[0,0,0],[0,0],[0]],[[219895800,8538408,2952],[8538408,10800],[2952]],[[0,0,0],[0,0],[0]],[[276951576,4599096,300],[4599096,1128],[300]],[[0,0,0],[0,0],[0]],[[262756896,1779336,12],[1779336,48],[12]],[[0,0],[0]],[[190956624,487800],[487800]],[[0,0],[0]],[[107137248,91920],[91920]],[[0,0],[0]],[[46454916,11232],[11232]],[[0,0],[0]],[[15486012,792],[792]],[[0,0],[0]],[[3920328,24],[24]],[[0]],[[737496]],[[0]],[[99444]],[[0]],[[9036]],[[0]],[[492]],[[0]],[[12]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
