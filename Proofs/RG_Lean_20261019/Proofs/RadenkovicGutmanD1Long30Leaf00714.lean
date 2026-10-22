/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00714 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10372639912460936603009810432000000000000 8250543132112927684329726431379050201088 76420826664965199449693356032000000000000))
theorem leaf00714_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10372639912460936603009810432000000000000 8250543132112927684329726431379050201088 76420826664965199449693356032000000000000 raw00714=true := by decide +kernel
#print axioms leaf00714_raw
theorem leaf00714_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00714=true := by decide +kernel
#print axioms leaf00714_rectangular
def affine00714 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00714 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00714_transform : affine00714=(NestedInteger.clearedAll 3 raw00714 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00714_transform
theorem leaf00714_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00714=true := by decide +kernel
#print axioms leaf00714_sign
theorem leaf00714_log : RationalLog.accepts (3083388471/4294967296) (-355853945/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00714_log
def leaf00714 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13495246473/125000000000) (3083388471/4294967296) (-355853945/2147483648) 1 8 ![60,0,4] ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00714
theorem leaf00714_checked : FastNestedCellData.accepts 1 2 4 leaf00714=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13495246473/125000000000) (3083388471/4294967296) (-355853945/2147483648) 1 8 ![60,0,4] ![(191/6400),0,(1/2)] ![(3/6400),1,(1/2)] 10372639912460936603009810432000000000000 8250543132112927684329726431379050201088 76420826664965199449693356032000000000000 raw00714 affine00714
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00714_raw leaf00714_rectangular
    leaf00714_transform leaf00714_sign leaf00714_log
#print axioms leaf00714_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
