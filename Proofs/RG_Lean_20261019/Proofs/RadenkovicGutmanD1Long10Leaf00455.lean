/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00455 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 20577410031244224614449020928000000000000 21850052358712165160187144856735938772992 6529204003262433468676160094208000000000000))
theorem leaf00455_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 20577410031244224614449020928000000000000 21850052358712165160187144856735938772992 6529204003262433468676160094208000000000000 raw00455=true := by decide +kernel
#print axioms leaf00455_raw
theorem leaf00455_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00455=true := by decide +kernel
#print axioms leaf00455_rectangular
def affine00455 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00455 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00455_transform : affine00455=(NestedInteger.clearedAll 3 raw00455 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00455_transform
theorem leaf00455_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00455=true := by decide +kernel
#print axioms leaf00455_sign
theorem leaf00455_log : RationalLog.accepts (4545385131/4294967296) (237685/8388608) 0 8=true := by decide +kernel
#print axioms leaf00455_log
def leaf00455 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (3346510899/1000000000000) (4545385131/4294967296) (237685/8388608) 0 8 ![52,0,4] ![(3/16),0,(3/4)] ![(1/64),1,(1/4)] affine00455
theorem leaf00455_checked : FastNestedCellData.accepts 1 0 4 leaf00455=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (3346510899/1000000000000) (4545385131/4294967296) (237685/8388608) 0 8 ![52,0,4] ![(3/16),0,(3/4)] ![(1/64),1,(1/4)] 20577410031244224614449020928000000000000 21850052358712165160187144856735938772992 6529204003262433468676160094208000000000000 raw00455 affine00455
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00455_raw leaf00455_rectangular
    leaf00455_transform leaf00455_sign leaf00455_log
#print axioms leaf00455_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
