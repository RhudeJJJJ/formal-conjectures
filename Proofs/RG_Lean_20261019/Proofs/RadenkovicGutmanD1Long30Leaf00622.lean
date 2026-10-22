/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00622 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5498447633889647652899913728000000000000 2899621719830765284417471090087314849792 9499943377805617598432280576000000000000))
theorem leaf00622_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5498447633889647652899913728000000000000 2899621719830765284417471090087314849792 9499943377805617598432280576000000000000 raw00622=true := by decide +kernel
#print axioms leaf00622_raw
theorem leaf00622_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00622=true := by decide +kernel
#print axioms leaf00622_rectangular
def affine00622 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00622 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00622_transform : affine00622=(NestedInteger.clearedAll 3 raw00622 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00622_transform
theorem leaf00622_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00622=true := by decide +kernel
#print axioms leaf00622_sign
theorem leaf00622_log : RationalLog.accepts (108456527/268435456) (-486545229/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00622_log
def leaf00622 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (152612579071/500000000000) (108456527/268435456) (-486545229/1073741824) 2 8 ![60,0,4] ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00622
theorem leaf00622_checked : FastNestedCellData.accepts 1 2 4 leaf00622=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (152612579071/500000000000) (108456527/268435456) (-486545229/1073741824) 2 8 ![60,0,4] ![(137/6400),0,(1/8)] ![(3/6400),1,(1/8)] 5498447633889647652899913728000000000000 2899621719830765284417471090087314849792 9499943377805617598432280576000000000000 raw00622 affine00622
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00622_raw leaf00622_rectangular
    leaf00622_transform leaf00622_sign leaf00622_log
#print axioms leaf00622_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
