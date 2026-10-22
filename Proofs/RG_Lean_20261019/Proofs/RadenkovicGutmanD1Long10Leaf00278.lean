/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00278 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 47999884156011304698264734924800000000000 32800607247634382299033617739763939278848 157569236363354424251202404352000000000000))
theorem leaf00278_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 47999884156011304698264734924800000000000 32800607247634382299033617739763939278848 157569236363354424251202404352000000000000 raw00278=true := by decide +kernel
#print axioms leaf00278_raw
theorem leaf00278_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00278=true := by decide +kernel
#print axioms leaf00278_rectangular
def affine00278 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00278 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00278_transform : affine00278=(NestedInteger.clearedAll 3 raw00278 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00278_transform
theorem leaf00278_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00278=true := by decide +kernel
#print axioms leaf00278_sign
theorem leaf00278_log : RationalLog.accepts (2429264665/4294967296) (-305938763/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00278_log
def leaf00278 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (52041578681/250000000000) (2429264665/4294967296) (-305938763/1073741824) 1 8 ![52,0,4] ![(1/16),0,(1/2)] ![(1/640),1,(1/2)] affine00278
theorem leaf00278_checked : FastNestedCellData.accepts 1 0 4 leaf00278=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (52041578681/250000000000) (2429264665/4294967296) (-305938763/1073741824) 1 8 ![52,0,4] ![(1/16),0,(1/2)] ![(1/640),1,(1/2)] 47999884156011304698264734924800000000000 32800607247634382299033617739763939278848 157569236363354424251202404352000000000000 raw00278 affine00278
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00278_raw leaf00278_rectangular
    leaf00278_transform leaf00278_sign leaf00278_log
#print axioms leaf00278_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
