/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00820 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3955349718785229636562321408000000000000 307118310173660562891762697857440677888 349687892498553733440864256000000000000))
theorem leaf00820_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3955349718785229636562321408000000000000 307118310173660562891762697857440677888 349687892498553733440864256000000000000 raw00820=true := by decide +kernel
#print axioms leaf00820_raw
theorem leaf00820_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00820=true := by decide +kernel
#print axioms leaf00820_rectangular
def affine00820 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00820 (IntegerComputedClassCell.leftNumerator ![(37/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/800),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00820_transform : affine00820=(NestedInteger.clearedAll 3 raw00820 (IntegerComputedClassCell.leftNumerator ![(37/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/800),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00820_transform
theorem leaf00820_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00820=true := by decide +kernel
#print axioms leaf00820_sign
theorem leaf00820_log : RationalLog.accepts (44387843/1073741824) (-855219073/536870912) 5 8=true := by decide +kernel
#print axioms leaf00820_log
def leaf00820 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (54891504103/62500000000) (44387843/1073741824) (-855219073/536870912) 5 8 ![60,0,4] ![(37/800),0,0] ![(3/3200),1,(1/16)] affine00820
theorem leaf00820_checked : FastNestedCellData.accepts 1 2 4 leaf00820=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (54891504103/62500000000) (44387843/1073741824) (-855219073/536870912) 5 8 ![60,0,4] ![(37/800),0,0] ![(3/3200),1,(1/16)] 3955349718785229636562321408000000000000 307118310173660562891762697857440677888 349687892498553733440864256000000000000 raw00820 affine00820
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00820_raw leaf00820_rectangular
    leaf00820_transform leaf00820_sign leaf00820_log
#print axioms leaf00820_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
