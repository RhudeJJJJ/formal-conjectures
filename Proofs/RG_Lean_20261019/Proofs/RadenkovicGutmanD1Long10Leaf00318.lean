/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00318 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 50711571716258452649797484544000000000000 11891071017340283020938557503795774881792 16896379643641923760289742848000000000000))
theorem leaf00318_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 50711571716258452649797484544000000000000 11891071017340283020938557503795774881792 16896379643641923760289742848000000000000 raw00318=true := by decide +kernel
#print axioms leaf00318_raw
theorem leaf00318_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00318=true := by decide +kernel
#print axioms leaf00318_rectangular
def affine00318 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00318 (IntegerComputedClassCell.leftNumerator ![(1/10),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/10),0,0] ![(1/320),1,(1/4)]))
theorem leaf00318_transform : affine00318=(NestedInteger.clearedAll 3 raw00318 (IntegerComputedClassCell.leftNumerator ![(1/10),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/10),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00318_transform
theorem leaf00318_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00318=true := by decide +kernel
#print axioms leaf00318_sign
theorem leaf00318_log : RationalLog.accepts (36944027/268435456) (-2129451833/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00318_log
def leaf00318 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (703764431679/1000000000000) (36944027/268435456) (-2129451833/2147483648) 3 8 ![52,0,4] ![(1/10),0,0] ![(1/320),1,(1/4)] affine00318
theorem leaf00318_checked : FastNestedCellData.accepts 1 0 4 leaf00318=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (703764431679/1000000000000) (36944027/268435456) (-2129451833/2147483648) 3 8 ![52,0,4] ![(1/10),0,0] ![(1/320),1,(1/4)] 50711571716258452649797484544000000000000 11891071017340283020938557503795774881792 16896379643641923760289742848000000000000 raw00318 affine00318
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00318_raw leaf00318_rectangular
    leaf00318_transform leaf00318_sign leaf00318_log
#print axioms leaf00318_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
