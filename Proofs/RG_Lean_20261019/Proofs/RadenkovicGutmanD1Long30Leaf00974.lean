/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00974 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5487538996497544357817090048000000000000 3661626627150123287784877699255863607296 12020324829857861574032621568000000000000))
theorem leaf00974_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5487538996497544357817090048000000000000 3661626627150123287784877699255863607296 12020324829857861574032621568000000000000 raw00974=true := by decide +kernel
#print axioms leaf00974_raw
theorem leaf00974_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00974=true := by decide +kernel
#print axioms leaf00974_rectangular
def affine00974 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00974 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00974_transform : affine00974=(NestedInteger.clearedAll 3 raw00974 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00974_transform
theorem leaf00974_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00974=true := by decide +kernel
#print axioms leaf00974_sign
theorem leaf00974_log : RationalLog.accepts (137294271/268435456) (-1439853273/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00974_log
def leaf00974 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (152309803561/500000000000) (137294271/268435456) (-1439853273/4294967296) 1 8 ![60,0,4] ![(9/80),0,(1/2)] ![(1/160),1,(1/2)] affine00974
theorem leaf00974_checked : FastNestedCellData.accepts 1 2 4 leaf00974=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (152309803561/500000000000) (137294271/268435456) (-1439853273/4294967296) 1 8 ![60,0,4] ![(9/80),0,(1/2)] ![(1/160),1,(1/2)] 5487538996497544357817090048000000000000 3661626627150123287784877699255863607296 12020324829857861574032621568000000000000 raw00974 affine00974
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00974_raw leaf00974_rectangular
    leaf00974_transform leaf00974_sign leaf00974_log
#print axioms leaf00974_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
