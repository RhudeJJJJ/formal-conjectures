/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00712 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 441468610253315203187867648000000000000 200797945170229364662124661128992653312 512105238086185835462393856000000000000))
theorem leaf00712_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 441468610253315203187867648000000000000 200797945170229364662124661128992653312 512105238086185835462393856000000000000 raw00712=true := by decide +kernel
#print axioms leaf00712_raw
theorem leaf00712_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00712=true := by decide +kernel
#print axioms leaf00712_rectangular
def affine00712 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00712 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00712_transform : affine00712=(NestedInteger.clearedAll 3 raw00712 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00712_transform
theorem leaf00712_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00712=true := by decide +kernel
#print axioms leaf00712_sign
theorem leaf00712_log : RationalLog.accepts (21926433/67108864) (-1201112595/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00712_log
def leaf00712 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (196051446301/500000000000) (21926433/67108864) (-1201112595/2147483648) 2 8 ![60,0,4] ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00712
theorem leaf00712_checked : FastNestedCellData.accepts 1 2 4 leaf00712=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (196051446301/500000000000) (21926433/67108864) (-1201112595/2147483648) 2 8 ![60,0,4] ![(191/6400),0,(1/8)] ![(3/6400),1,(1/8)] 441468610253315203187867648000000000000 200797945170229364662124661128992653312 512105238086185835462393856000000000000 raw00712 affine00712
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00712_raw leaf00712_rectangular
    leaf00712_transform leaf00712_sign leaf00712_log
#print axioms leaf00712_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
