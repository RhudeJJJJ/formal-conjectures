/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00345 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 139848707181526318297358165606400000000000 292956415209238695158415032825765953536 483030208593705752065998848000000000000))
theorem leaf00345_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 139848707181526318297358165606400000000000 292956415209238695158415032825765953536 483030208593705752065998848000000000000 raw00345=true := by decide +kernel
#print axioms leaf00345_raw
theorem leaf00345_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00345=true := by decide +kernel
#print axioms leaf00345_rectangular
def affine00345 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00345 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00345_transform : affine00345=(NestedInteger.clearedAll 3 raw00345 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00345_transform
theorem leaf00345_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00345=true := by decide +kernel
#print axioms leaf00345_sign
theorem leaf00345_log : RationalLog.accepts (2800235/2147483648) (-3566083891/1073741824) 10 8=true := by decide +kernel
#print axioms leaf00345_log
def leaf00345 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (303248544291/500000000000) (2800235/2147483648) (-3566083891/1073741824) 10 8 ![60,0,4] ![(53/6400),0,0] ![(1/6400),1,(1/16)] affine00345
theorem leaf00345_checked : FastNestedCellData.accepts 1 2 4 leaf00345=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (303248544291/500000000000) (2800235/2147483648) (-3566083891/1073741824) 10 8 ![60,0,4] ![(53/6400),0,0] ![(1/6400),1,(1/16)] 139848707181526318297358165606400000000000 292956415209238695158415032825765953536 483030208593705752065998848000000000000 raw00345 affine00345
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00345_raw leaf00345_rectangular
    leaf00345_transform leaf00345_sign leaf00345_log
#print axioms leaf00345_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
