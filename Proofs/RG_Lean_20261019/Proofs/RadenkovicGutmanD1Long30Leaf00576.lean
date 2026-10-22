/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00576 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 545374203873775679750249906176000000000000 197054926818185759050255988850162386599936 416574273413923058994418548736000000000000))
theorem leaf00576_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 545374203873775679750249906176000000000000 197054926818185759050255988850162386599936 416574273413923058994418548736000000000000 raw00576=true := by decide +kernel
#print axioms leaf00576_raw
theorem leaf00576_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00576=true := by decide +kernel
#print axioms leaf00576_rectangular
def affine00576 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00576 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00576_transform : affine00576=(NestedInteger.clearedAll 3 raw00576 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00576_transform
theorem leaf00576_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00576=true := by decide +kernel
#print axioms leaf00576_sign
theorem leaf00576_log : RationalLog.accepts (526755403/2147483648) (-3017892657/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00576_log
def leaf00576 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (236518358663/500000000000) (526755403/2147483648) (-3017892657/4294967296) 3 8 ![60,0,4] ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)] affine00576
theorem leaf00576_checked : FastNestedCellData.accepts 1 2 4 leaf00576=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (236518358663/500000000000) (526755403/2147483648) (-3017892657/4294967296) 3 8 ![60,0,4] ![(29/1600),0,(1/16)] ![(1/3200),1,(1/16)] 545374203873775679750249906176000000000000 197054926818185759050255988850162386599936 416574273413923058994418548736000000000000 raw00576 affine00576
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00576_raw leaf00576_rectangular
    leaf00576_transform leaf00576_sign leaf00576_log
#print axioms leaf00576_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
