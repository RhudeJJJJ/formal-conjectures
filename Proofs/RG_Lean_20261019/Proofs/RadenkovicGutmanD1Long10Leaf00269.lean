/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00269 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 563074054503116278450125537280000000000 390158125237173616814545669055768952832 1997169329618522438826459136000000000000))
theorem leaf00269_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 563074054503116278450125537280000000000 390158125237173616814545669055768952832 1997169329618522438826459136000000000000 raw00269=true := by decide +kernel
#print axioms leaf00269_raw
theorem leaf00269_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00269=true := by decide +kernel
#print axioms leaf00269_rectangular
def affine00269 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00269 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00269_transform : affine00269=(NestedInteger.clearedAll 3 raw00269 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00269_transform
theorem leaf00269_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00269=true := by decide +kernel
#print axioms leaf00269_sign
theorem leaf00269_log : RationalLog.accepts (622411925/1073741824) (-292757181/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00269_log
def leaf00269 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (48838889053/250000000000) (622411925/1073741824) (-292757181/1073741824) 1 8 ![52,0,4] ![(37/640),0,(1/2)] ![(1/640),1,(1/2)] affine00269
theorem leaf00269_checked : FastNestedCellData.accepts 1 0 4 leaf00269=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (48838889053/250000000000) (622411925/1073741824) (-292757181/1073741824) 1 8 ![52,0,4] ![(37/640),0,(1/2)] ![(1/640),1,(1/2)] 563074054503116278450125537280000000000 390158125237173616814545669055768952832 1997169329618522438826459136000000000000 raw00269 affine00269
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00269_raw leaf00269_rectangular
    leaf00269_transform leaf00269_sign leaf00269_log
#print axioms leaf00269_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
