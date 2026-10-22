/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00110 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 195796712437262879738656980992000000000000 177313354029301408881677204317863042613248 4176339354622240435830811262976000000000000))
theorem leaf00110_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 195796712437262879738656980992000000000000 177313354029301408881677204317863042613248 4176339354622240435830811262976000000000000 raw00110=true := by decide +kernel
#print axioms leaf00110_raw
theorem leaf00110_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00110=true := by decide +kernel
#print axioms leaf00110_rectangular
def affine00110 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00110 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00110_transform : affine00110=(NestedInteger.clearedAll 3 raw00110 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00110_transform
theorem leaf00110_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00110=true := by decide +kernel
#print axioms leaf00110_sign
theorem leaf00110_log : RationalLog.accepts (3731108763/4294967296) (-302233655/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00110_log
def leaf00110 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (21228322099/500000000000) (3731108763/4294967296) (-302233655/4294967296) 1 8 ![52,0,4] ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00110
theorem leaf00110_checked : FastNestedCellData.accepts 1 0 4 leaf00110=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (21228322099/500000000000) (3731108763/4294967296) (-302233655/4294967296) 1 8 ![52,0,4] ![(37/3200),0,(1/2)] ![(1/3200),1,(1/2)] 195796712437262879738656980992000000000000 177313354029301408881677204317863042613248 4176339354622240435830811262976000000000000 raw00110 affine00110
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00110_raw leaf00110_rectangular
    leaf00110_transform leaf00110_sign leaf00110_log
#print axioms leaf00110_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
