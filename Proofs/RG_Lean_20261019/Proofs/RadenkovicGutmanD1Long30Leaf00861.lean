/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00861 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 835473635702026471655453229056000000000000 218569594149636439008725083936527709372416 301617638881642476674048065536000000000000))
theorem leaf00861_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 835473635702026471655453229056000000000000 218569594149636439008725083936527709372416 301617638881642476674048065536000000000000 raw00861=true := by decide +kernel
#print axioms leaf00861_raw
theorem leaf00861_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00861=true := by decide +kernel
#print axioms leaf00861_rectangular
def affine00861 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00861 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00861_transform : affine00861=(NestedInteger.clearedAll 3 raw00861 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00861_transform
theorem leaf00861_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00861=true := by decide +kernel
#print axioms leaf00861_sign
theorem leaf00861_log : RationalLog.accepts (325749613/2147483648) (-4049988935/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00861_log
def leaf00861 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (362328932353/500000000000) (325749613/2147483648) (-4049988935/4294967296) 3 8 ![60,0,4] ![(9/160),0,(1/16)] ![(1/640),1,(1/16)] affine00861
theorem leaf00861_checked : FastNestedCellData.accepts 1 2 4 leaf00861=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (362328932353/500000000000) (325749613/2147483648) (-4049988935/4294967296) 3 8 ![60,0,4] ![(9/160),0,(1/16)] ![(1/640),1,(1/16)] 835473635702026471655453229056000000000000 218569594149636439008725083936527709372416 301617638881642476674048065536000000000000 raw00861 affine00861
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00861_raw leaf00861_rectangular
    leaf00861_transform leaf00861_sign leaf00861_log
#print axioms leaf00861_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
