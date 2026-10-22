/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00181 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 14024207361234363163294564352000000000000 9285828830457983404069641827371116920832 47711394087083388393882648576000000000000))
theorem leaf00181_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 14024207361234363163294564352000000000000 9285828830457983404069641827371116920832 47711394087083388393882648576000000000000 raw00181=true := by decide +kernel
#print axioms leaf00181_raw
theorem leaf00181_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00181=true := by decide +kernel
#print axioms leaf00181_rectangular
def affine00181 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00181 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00181_transform : affine00181=(NestedInteger.clearedAll 3 raw00181 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00181_transform
theorem leaf00181_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00181=true := by decide +kernel
#print axioms leaf00181_sign
theorem leaf00181_log : RationalLog.accepts (595128337/1073741824) (-633644901/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00181_log
def leaf00181 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (48656243483/250000000000) (595128337/1073741824) (-633644901/2147483648) 1 8 ![52,0,4] ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)] affine00181
theorem leaf00181_checked : FastNestedCellData.accepts 1 0 4 leaf00181=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (48656243483/250000000000) (595128337/1073741824) (-633644901/2147483648) 1 8 ![52,0,4] ![(17/640),0,(1/4)] ![(3/3200),1,(1/4)] 14024207361234363163294564352000000000000 9285828830457983404069641827371116920832 47711394087083388393882648576000000000000 raw00181 affine00181
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00181_raw leaf00181_rectangular
    leaf00181_transform leaf00181_sign leaf00181_log
#print axioms leaf00181_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
