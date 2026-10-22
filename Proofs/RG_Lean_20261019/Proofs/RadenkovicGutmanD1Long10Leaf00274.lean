/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00274 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 26777705895945950064902406144000000000000 13981316055978307608804585065829522997248 37623088415134714815013978112000000000000))
theorem leaf00274_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 26777705895945950064902406144000000000000 13981316055978307608804585065829522997248 37623088415134714815013978112000000000000 raw00274=true := by decide +kernel
#print axioms leaf00274_raw
theorem leaf00274_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00274=true := by decide +kernel
#print axioms leaf00274_rectangular
def affine00274 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00274 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00274_transform : affine00274=(NestedInteger.clearedAll 3 raw00274 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00274_transform
theorem leaf00274_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00274=true := by decide +kernel
#print axioms leaf00274_sign
theorem leaf00274_log : RationalLog.accepts (408735377/1073741824) (-2074119047/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00274_log
def leaf00274 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (92903830101/250000000000) (408735377/1073741824) (-2074119047/4294967296) 2 8 ![52,0,4] ![(39/640),0,(1/4)] ![(1/640),1,(1/4)] affine00274
theorem leaf00274_checked : FastNestedCellData.accepts 1 0 4 leaf00274=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (92903830101/250000000000) (408735377/1073741824) (-2074119047/4294967296) 2 8 ![52,0,4] ![(39/640),0,(1/4)] ![(1/640),1,(1/4)] 26777705895945950064902406144000000000000 13981316055978307608804585065829522997248 37623088415134714815013978112000000000000 raw00274 affine00274
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00274_raw leaf00274_rectangular
    leaf00274_transform leaf00274_sign leaf00274_log
#print axioms leaf00274_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
