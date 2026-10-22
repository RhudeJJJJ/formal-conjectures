/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00046 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 179869683200258771721736159232000000000000 163726243590202536808745250426634723393536 4197783723085400470340807688192000000000000))
theorem leaf00046_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 179869683200258771721736159232000000000000 163726243590202536808745250426634723393536 4197783723085400470340807688192000000000000 raw00046=true := by decide +kernel
#print axioms leaf00046_raw
theorem leaf00046_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00046=true := by decide +kernel
#print axioms leaf00046_rectangular
def affine00046 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00046 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00046_transform : affine00046=(NestedInteger.clearedAll 3 raw00046 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00046_transform
theorem leaf00046_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00046=true := by decide +kernel
#print axioms leaf00046_sign
theorem leaf00046_log : RationalLog.accepts (3762732801/4294967296) (-142054385/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00046_log
def leaf00046 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (19501510129/500000000000) (3762732801/4294967296) (-142054385/2147483648) 1 8 ![52,0,4] ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)] affine00046
theorem leaf00046_checked : FastNestedCellData.accepts 1 0 4 leaf00046=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (19501510129/500000000000) (3762732801/4294967296) (-142054385/2147483648) 1 8 ![52,0,4] ![(1/200),0,(1/4)] ![(1/3200),1,(1/4)] 179869683200258771721736159232000000000000 163726243590202536808745250426634723393536 4197783723085400470340807688192000000000000 raw00046 affine00046
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00046_raw leaf00046_rectangular
    leaf00046_transform leaf00046_sign leaf00046_log
#print axioms leaf00046_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
