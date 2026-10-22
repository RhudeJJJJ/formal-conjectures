/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00244 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1416741619548393287913792602112000000000000 791559700874449760570998066797345188610048 2576634126437882612502092578816000000000000))
theorem leaf00244_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1416741619548393287913792602112000000000000 791559700874449760570998066797345188610048 2576634126437882612502092578816000000000000 raw00244=true := by decide +kernel
#print axioms leaf00244_raw
theorem leaf00244_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00244=true := by decide +kernel
#print axioms leaf00244_rectangular
def affine00244 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00244 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00244_transform : affine00244=(NestedInteger.clearedAll 3 raw00244 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00244_transform
theorem leaf00244_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00244=true := by decide +kernel
#print axioms leaf00244_sign
theorem leaf00244_log : RationalLog.accepts (917864489/2147483648) (-912683029/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00244_log
def leaf00244 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (307206868353/1000000000000) (917864489/2147483648) (-912683029/2147483648) 2 8 ![52,0,4] ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)] affine00244
theorem leaf00244_checked : FastNestedCellData.accepts 1 0 4 leaf00244=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (307206868353/1000000000000) (917864489/2147483648) (-912683029/2147483648) 2 8 ![52,0,4] ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)] 1416741619548393287913792602112000000000000 791559700874449760570998066797345188610048 2576634126437882612502092578816000000000000 raw00244 affine00244
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00244_raw leaf00244_rectangular
    leaf00244_transform leaf00244_sign leaf00244_log
#print axioms leaf00244_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
