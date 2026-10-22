/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00137 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 17872380594285859791844671488000000000000 15491530579075719558552760902854123716608 249834075679897195084517474304000000000000))
theorem leaf00137_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 17872380594285859791844671488000000000000 15491530579075719558552760902854123716608 249834075679897195084517474304000000000000 raw00137=true := by decide +kernel
#print axioms leaf00137_raw
theorem leaf00137_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00137=true := by decide +kernel
#print axioms leaf00137_rectangular
def affine00137 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00137 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00137_transform : affine00137=(NestedInteger.clearedAll 3 raw00137 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00137_transform
theorem leaf00137_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00137=true := by decide +kernel
#print axioms leaf00137_sign
theorem leaf00137_log : RationalLog.accepts (438181771/536870912) (-218102593/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00137_log
def leaf00137 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (62007276377/1000000000000) (438181771/536870912) (-218102593/2147483648) 1 8 ![52,0,4] ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)] affine00137
theorem leaf00137_checked : FastNestedCellData.accepts 1 0 4 leaf00137=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (62007276377/1000000000000) (438181771/536870912) (-218102593/2147483648) 1 8 ![52,0,4] ![(27/1600),0,(1/2)] ![(1/1600),1,(1/2)] 17872380594285859791844671488000000000000 15491530579075719558552760902854123716608 249834075679897195084517474304000000000000 raw00137 affine00137
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00137_raw leaf00137_rectangular
    leaf00137_transform leaf00137_sign leaf00137_log
#print axioms leaf00137_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
