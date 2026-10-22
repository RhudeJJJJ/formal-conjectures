/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00246 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 746690977729823455360879427584000000000000 518036809805812762260383660139793889624064 3199480352736522850451570294784000000000000))
theorem leaf00246_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 746690977729823455360879427584000000000000 518036809805812762260383660139793889624064 3199480352736522850451570294784000000000000 raw00246=true := by decide +kernel
#print axioms leaf00246_raw
theorem leaf00246_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00246=true := by decide +kernel
#print axioms leaf00246_rectangular
def affine00246 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00246 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00246_transform : affine00246=(NestedInteger.clearedAll 3 raw00246 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00246_transform
theorem leaf00246_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00246=true := by decide +kernel
#print axioms leaf00246_sign
theorem leaf00246_log : RationalLog.accepts (2564519721/4294967296) (-138424847/536870912) 1 8=true := by decide +kernel
#print axioms leaf00246_log
def leaf00246 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (80956398023/500000000000) (2564519721/4294967296) (-138424847/536870912) 1 8 ![60,0,4] ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00246
theorem leaf00246_checked : FastNestedCellData.accepts 1 2 4 leaf00246=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (80956398023/500000000000) (2564519721/4294967296) (-138424847/536870912) 1 8 ![60,0,4] ![(33/6400),0,(1/16)] ![(1/6400),1,(1/16)] 746690977729823455360879427584000000000000 518036809805812762260383660139793889624064 3199480352736522850451570294784000000000000 raw00246 affine00246
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00246_raw leaf00246_rectangular
    leaf00246_transform leaf00246_sign leaf00246_log
#print axioms leaf00246_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
