/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00399 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 673677079972614914281966665728000000000000 619424447884444057615276035466235706605568 16961188977347519438727828996096000000000000))
theorem leaf00399_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 673677079972614914281966665728000000000000 619424447884444057615276035466235706605568 16961188977347519438727828996096000000000000 raw00399=true := by decide +kernel
#print axioms leaf00399_raw
theorem leaf00399_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00399=true := by decide +kernel
#print axioms leaf00399_rectangular
def affine00399 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00399 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00399_transform : affine00399=(NestedInteger.clearedAll 3 raw00399 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00399_transform
theorem leaf00399_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00399=true := by decide +kernel
#print axioms leaf00399_sign
theorem leaf00399_log : RationalLog.accepts (3809944947/4294967296) (-257331287/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00399_log
def leaf00399 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (36520107683/1000000000000) (3809944947/4294967296) (-257331287/4294967296) 1 8 ![60,0,4] ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00399
theorem leaf00399_checked : FastNestedCellData.accepts 1 2 4 leaf00399=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (36520107683/1000000000000) (3809944947/4294967296) (-257331287/4294967296) 1 8 ![60,0,4] ![(63/6400),0,(1/2)] ![(1/6400),1,(1/2)] 673677079972614914281966665728000000000000 619424447884444057615276035466235706605568 16961188977347519438727828996096000000000000 raw00399 affine00399
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00399_raw leaf00399_rectangular
    leaf00399_transform leaf00399_sign leaf00399_log
#print axioms leaf00399_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
