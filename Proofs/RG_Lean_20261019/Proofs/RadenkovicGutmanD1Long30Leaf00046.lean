/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00046 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 37018465879652720964365493207040000000000 32932559156175438713887004903598167425024 656427516387362072804756291584000000000000))
theorem leaf00046_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 37018465879652720964365493207040000000000 32932559156175438713887004903598167425024 656427516387362072804756291584000000000000 raw00046=true := by decide +kernel
#print axioms leaf00046_raw
theorem leaf00046_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00046=true := by decide +kernel
#print axioms leaf00046_rectangular
def affine00046 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00046 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00046_transform : affine00046=(NestedInteger.clearedAll 3 raw00046 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00046_transform
theorem leaf00046_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00046=true := by decide +kernel
#print axioms leaf00046_sign
theorem leaf00046_log : RationalLog.accepts (3638375975/4294967296) (-178140787/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00046_log
def leaf00046 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (50169376411/1000000000000) (3638375975/4294967296) (-178140787/2147483648) 1 8 ![60,0,4] ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)] affine00046
theorem leaf00046_checked : FastNestedCellData.accepts 1 2 4 leaf00046=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (50169376411/1000000000000) (3638375975/4294967296) (-178140787/2147483648) 1 8 ![60,0,4] ![(1/640),0,(1/16)] ![(1/16000),1,(1/16)] 37018465879652720964365493207040000000000 32932559156175438713887004903598167425024 656427516387362072804756291584000000000000 raw00046 affine00046
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00046_raw leaf00046_rectangular
    leaf00046_transform leaf00046_sign leaf00046_log
#print axioms leaf00046_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
