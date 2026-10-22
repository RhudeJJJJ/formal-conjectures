/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00723 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2107504190511617394931138560000000000 1348733601439736445901169838803386368 6148599767466435992291901440000000000))
theorem leaf00723_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2107504190511617394931138560000000000 1348733601439736445901169838803386368 6148599767466435992291901440000000000 raw00723=true := by decide +kernel
#print axioms leaf00723_raw
theorem leaf00723_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00723=true := by decide +kernel
#print axioms leaf00723_rectangular
def affine00723 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00723 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00723_transform : affine00723=(NestedInteger.clearedAll 3 raw00723 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00723_transform
theorem leaf00723_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00723=true := by decide +kernel
#print axioms leaf00723_sign
theorem leaf00723_log : RationalLog.accepts (281771463/536870912) (-1384399745/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00723_log
def leaf00723 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2193562197/10000000000) (281771463/536870912) (-1384399745/4294967296) 1 8 ![60,0,4] ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00723
theorem leaf00723_checked : FastNestedCellData.accepts 1 2 4 leaf00723=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2193562197/10000000000) (281771463/536870912) (-1384399745/4294967296) 1 8 ![60,0,4] ![(197/6400),0,(1/4)] ![(3/6400),1,(1/4)] 2107504190511617394931138560000000000 1348733601439736445901169838803386368 6148599767466435992291901440000000000 raw00723 affine00723
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00723_raw leaf00723_rectangular
    leaf00723_transform leaf00723_sign leaf00723_log
#print axioms leaf00723_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
