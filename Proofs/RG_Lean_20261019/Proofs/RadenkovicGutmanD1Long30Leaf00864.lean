/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00864 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1175230833100950677257281601536000000000000 821399059256298621274521253198893913473024 4297634643827507552040148533248000000000000))
theorem leaf00864_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1175230833100950677257281601536000000000000 821399059256298621274521253198893913473024 4297634643827507552040148533248000000000000 raw00864=true := by decide +kernel
#print axioms leaf00864_raw
theorem leaf00864_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00864=true := by decide +kernel
#print axioms leaf00864_rectangular
def affine00864 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00864 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00864_transform : affine00864=(NestedInteger.clearedAll 3 raw00864 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00864_transform
theorem leaf00864_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00864=true := by decide +kernel
#print axioms leaf00864_sign
theorem leaf00864_log : RationalLog.accepts (2520184803/4294967296) (-572424355/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00864_log
def leaf00864 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (191128173363/1000000000000) (2520184803/4294967296) (-572424355/2147483648) 1 8 ![60,0,4] ![(9/160),0,(1/2)] ![(1/640),1,(1/2)] affine00864
theorem leaf00864_checked : FastNestedCellData.accepts 1 2 4 leaf00864=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (191128173363/1000000000000) (2520184803/4294967296) (-572424355/2147483648) 1 8 ![60,0,4] ![(9/160),0,(1/2)] ![(1/640),1,(1/2)] 1175230833100950677257281601536000000000000 821399059256298621274521253198893913473024 4297634643827507552040148533248000000000000 raw00864 affine00864
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00864_raw leaf00864_rectangular
    leaf00864_transform leaf00864_sign leaf00864_log
#print axioms leaf00864_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
