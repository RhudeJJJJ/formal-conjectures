/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00185 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 114848073076209213943807213568000000000000 92287176186662754160584932969620998979584 926440184629315659684630233088000000000000))
theorem leaf00185_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 114848073076209213943807213568000000000000 92287176186662754160584932969620998979584 926440184629315659684630233088000000000000 raw00185=true := by decide +kernel
#print axioms leaf00185_raw
theorem leaf00185_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00185=true := by decide +kernel
#print axioms leaf00185_rectangular
def affine00185 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00185 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00185_transform : affine00185=(NestedInteger.clearedAll 3 raw00185 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00185_transform
theorem leaf00185_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00185=true := by decide +kernel
#print axioms leaf00185_sign
theorem leaf00185_log : RationalLog.accepts (3138606861/4294967296) (-336795155/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00185_log
def leaf00185 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (24903706067/250000000000) (3138606861/4294967296) (-336795155/2147483648) 1 8 ![52,0,4] ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)] affine00185
theorem leaf00185_checked : FastNestedCellData.accepts 1 0 4 leaf00185=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (24903706067/250000000000) (3138606861/4294967296) (-336795155/2147483648) 1 8 ![52,0,4] ![(11/400),0,(1/2)] ![(3/3200),1,(1/2)] 114848073076209213943807213568000000000000 92287176186662754160584932969620998979584 926440184629315659684630233088000000000000 raw00185 affine00185
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00185_raw leaf00185_rectangular
    leaf00185_transform leaf00185_sign leaf00185_log
#print axioms leaf00185_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
