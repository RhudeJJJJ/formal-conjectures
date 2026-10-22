/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00295 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 38358529988127560302592000000000000 19564540141336977862627596290752512 46733280672617820848128000000000000))
theorem leaf00295_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 38358529988127560302592000000000000 19564540141336977862627596290752512 46733280672617820848128000000000000 raw00295=true := by decide +kernel
#print axioms leaf00295_raw
theorem leaf00295_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00295=true := by decide +kernel
#print axioms leaf00295_rectangular
def affine00295 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00295 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00295_transform : affine00295=(NestedInteger.clearedAll 3 raw00295 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00295_transform
theorem leaf00295_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00295=true := by decide +kernel
#print axioms leaf00295_sign
theorem leaf00295_log : RationalLog.accepts (12063813/33554432) (-2196787035/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00295_log
def leaf00295 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (6541289961/15625000000) (12063813/33554432) (-2196787035/4294967296) 2 8 ![52,0,4] ![(3/40),0,(1/4)] ![(1/320),1,(1/4)] affine00295
theorem leaf00295_checked : FastNestedCellData.accepts 1 0 4 leaf00295=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (6541289961/15625000000) (12063813/33554432) (-2196787035/4294967296) 2 8 ![52,0,4] ![(3/40),0,(1/4)] ![(1/320),1,(1/4)] 38358529988127560302592000000000000 19564540141336977862627596290752512 46733280672617820848128000000000000 raw00295 affine00295
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00295_raw leaf00295_rectangular
    leaf00295_transform leaf00295_sign leaf00295_log
#print axioms leaf00295_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
