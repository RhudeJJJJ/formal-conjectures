/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00299 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 462261928945452973898067869696000000000000 435930181653653757664733015230483028508672 17395965342236876992400811098112000000000000))
theorem leaf00299_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 462261928945452973898067869696000000000000 435930181653653757664733015230483028508672 17395965342236876992400811098112000000000000 raw00299=true := by decide +kernel
#print axioms leaf00299_raw
theorem leaf00299_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00299=true := by decide +kernel
#print axioms leaf00299_rectangular
def affine00299 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00299 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00299_transform : affine00299=(NestedInteger.clearedAll 3 raw00299 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00299_transform
theorem leaf00299_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00299=true := by decide +kernel
#print axioms leaf00299_sign
theorem leaf00299_log : RationalLog.accepts (3951297187/4294967296) (-179100203/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00299_log
def leaf00299 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (25059269381/1000000000000) (3951297187/4294967296) (-179100203/4294967296) 1 8 ![60,0,4] ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00299
theorem leaf00299_checked : FastNestedCellData.accepts 1 2 4 leaf00299=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (25059269381/1000000000000) (3951297187/4294967296) (-179100203/4294967296) 1 8 ![60,0,4] ![(43/6400),0,(1/2)] ![(1/6400),1,(1/2)] 462261928945452973898067869696000000000000 435930181653653757664733015230483028508672 17395965342236876992400811098112000000000000 raw00299 affine00299
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00299_raw leaf00299_rectangular
    leaf00299_transform leaf00299_sign leaf00299_log
#print axioms leaf00299_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
