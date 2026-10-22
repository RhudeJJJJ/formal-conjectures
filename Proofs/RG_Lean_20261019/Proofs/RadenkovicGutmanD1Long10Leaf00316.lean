/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00316 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8550721270118048527019413602304000000000000 4459483492076403586728627355155596696354816 9620586156485753162684237348864000000000000))
theorem leaf00316_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8550721270118048527019413602304000000000000 4459483492076403586728627355155596696354816 9620586156485753162684237348864000000000000 raw00316=true := by decide +kernel
#print axioms leaf00316_raw
theorem leaf00316_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00316=true := by decide +kernel
#print axioms leaf00316_rectangular
def affine00316 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00316 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00316_transform : affine00316=(NestedInteger.clearedAll 3 raw00316 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00316_transform
theorem leaf00316_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00316=true := by decide +kernel
#print axioms leaf00316_sign
theorem leaf00316_log : RationalLog.accepts (1530517861/4294967296) (-276981857/536870912) 2 8=true := by decide +kernel
#print axioms leaf00316_log
def leaf00316 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (463535528869/1000000000000) (1530517861/4294967296) (-276981857/536870912) 2 8 ![52,0,4] ![(31/320),0,(1/4)] ![(1/320),1,(1/4)] affine00316
theorem leaf00316_checked : FastNestedCellData.accepts 1 0 4 leaf00316=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (463535528869/1000000000000) (1530517861/4294967296) (-276981857/536870912) 2 8 ![52,0,4] ![(31/320),0,(1/4)] ![(1/320),1,(1/4)] 8550721270118048527019413602304000000000000 4459483492076403586728627355155596696354816 9620586156485753162684237348864000000000000 raw00316 affine00316
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00316_raw leaf00316_rectangular
    leaf00316_transform leaf00316_sign leaf00316_log
#print axioms leaf00316_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
