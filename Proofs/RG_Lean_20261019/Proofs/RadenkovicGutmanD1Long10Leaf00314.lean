/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00314 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 323964717908454524838815465472000000000000 211150225631963142111804717594322485116928 751438728900314964774275252224000000000000))
theorem leaf00314_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 323964717908454524838815465472000000000000 211150225631963142111804717594322485116928 751438728900314964774275252224000000000000 raw00314=true := by decide +kernel
#print axioms leaf00314_raw
theorem leaf00314_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00314=true := by decide +kernel
#print axioms leaf00314_rectangular
def affine00314 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00314 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00314_transform : affine00314=(NestedInteger.clearedAll 3 raw00314 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00314_transform
theorem leaf00314_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00314=true := by decide +kernel
#print axioms leaf00314_sign
theorem leaf00314_log : RationalLog.accepts (2185276507/4294967296) (-725529057/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00314_log
def leaf00314 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (70248650193/250000000000) (2185276507/4294967296) (-725529057/2147483648) 1 8 ![52,0,4] ![(3/32),0,(1/2)] ![(1/320),1,(1/2)] affine00314
theorem leaf00314_checked : FastNestedCellData.accepts 1 0 4 leaf00314=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (70248650193/250000000000) (2185276507/4294967296) (-725529057/2147483648) 1 8 ![52,0,4] ![(3/32),0,(1/2)] ![(1/320),1,(1/2)] 323964717908454524838815465472000000000000 211150225631963142111804717594322485116928 751438728900314964774275252224000000000000 raw00314 affine00314
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00314_raw leaf00314_rectangular
    leaf00314_transform leaf00314_sign leaf00314_log
#print axioms leaf00314_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
