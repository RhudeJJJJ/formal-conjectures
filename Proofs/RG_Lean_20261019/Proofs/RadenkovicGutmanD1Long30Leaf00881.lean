/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00881 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 13449230363292741148127591923712000000000000 3672522155423232076781029512012848437395456 5037171234052268412221006020608000000000000))
theorem leaf00881_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 13449230363292741148127591923712000000000000 3672522155423232076781029512012848437395456 5037171234052268412221006020608000000000000 raw00881=true := by decide +kernel
#print axioms leaf00881_raw
theorem leaf00881_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00881=true := by decide +kernel
#print axioms leaf00881_rectangular
def affine00881 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00881 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00881_transform : affine00881=(NestedInteger.clearedAll 3 raw00881 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00881_transform
theorem leaf00881_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00881=true := by decide +kernel
#print axioms leaf00881_sign
theorem leaf00881_log : RationalLog.accepts (678282639/4294967296) (-3963471405/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00881_log
def leaf00881 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (729084238907/1000000000000) (678282639/4294967296) (-3963471405/4294967296) 3 8 ![60,0,4] ![(1/16),0,(1/16)] ![(1/640),1,(1/16)] affine00881
theorem leaf00881_checked : FastNestedCellData.accepts 1 2 4 leaf00881=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (729084238907/1000000000000) (678282639/4294967296) (-3963471405/4294967296) 3 8 ![60,0,4] ![(1/16),0,(1/16)] ![(1/640),1,(1/16)] 13449230363292741148127591923712000000000000 3672522155423232076781029512012848437395456 5037171234052268412221006020608000000000000 raw00881 affine00881
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00881_raw leaf00881_rectangular
    leaf00881_transform leaf00881_sign leaf00881_log
#print axioms leaf00881_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
