/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00562 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 379682969881048610005581824000000000000 221278703453405382528322980410579484672 874897186574713175823876096000000000000))
theorem leaf00562_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 379682969881048610005581824000000000000 221278703453405382528322980410579484672 874897186574713175823876096000000000000 raw00562=true := by decide +kernel
#print axioms leaf00562_raw
theorem leaf00562_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00562=true := by decide +kernel
#print axioms leaf00562_rectangular
def affine00562 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00562 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00562_transform : affine00562=(NestedInteger.clearedAll 3 raw00562 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00562_transform
theorem leaf00562_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00562=true := by decide +kernel
#print axioms leaf00562_sign
theorem leaf00562_log : RationalLog.accepts (124863399/268435456) (-1643662937/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00562_log
def leaf00562 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (63229916283/250000000000) (124863399/268435456) (-1643662937/4294967296) 2 8 ![60,0,4] ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)] affine00562
theorem leaf00562_checked : FastNestedCellData.accepts 1 2 4 leaf00562=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (63229916283/250000000000) (124863399/268435456) (-1643662937/4294967296) 2 8 ![60,0,4] ![(11/640),0,(1/8)] ![(1/3200),1,(1/8)] 379682969881048610005581824000000000000 221278703453405382528322980410579484672 874897186574713175823876096000000000000 raw00562 affine00562
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00562_raw leaf00562_rectangular
    leaf00562_transform leaf00562_sign leaf00562_log
#print axioms leaf00562_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
