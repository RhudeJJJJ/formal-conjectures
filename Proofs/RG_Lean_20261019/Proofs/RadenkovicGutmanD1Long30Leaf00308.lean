/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00308 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3109600637970567635307121868800000000000 2747462382941089624686593763874348990464 50932721483785848787895844864000000000000))
theorem leaf00308_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3109600637970567635307121868800000000000 2747462382941089624686593763874348990464 50932721483785848787895844864000000000000 raw00308=true := by decide +kernel
#print axioms leaf00308_raw
theorem leaf00308_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00308=true := by decide +kernel
#print axioms leaf00308_rectangular
def affine00308 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00308 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00308_transform : affine00308=(NestedInteger.clearedAll 3 raw00308 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00308_transform
theorem leaf00308_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00308=true := by decide +kernel
#print axioms leaf00308_sign
theorem leaf00308_log : RationalLog.accepts (1800279315/2147483648) (-189359685/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00308_log
def leaf00308 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13485743069/250000000000) (1800279315/2147483648) (-189359685/2147483648) 1 8 ![60,0,4] ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)] affine00308
theorem leaf00308_checked : FastNestedCellData.accepts 1 2 4 leaf00308=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13485743069/250000000000) (1800279315/2147483648) (-189359685/2147483648) 1 8 ![60,0,4] ![(9/1280),0,(1/4)] ![(1/6400),1,(1/4)] 3109600637970567635307121868800000000000 2747462382941089624686593763874348990464 50932721483785848787895844864000000000000 raw00308 affine00308
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00308_raw leaf00308_rectangular
    leaf00308_transform leaf00308_sign leaf00308_log
#print axioms leaf00308_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
