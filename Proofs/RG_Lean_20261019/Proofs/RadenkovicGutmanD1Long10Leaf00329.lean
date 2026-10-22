/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00329 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1449451270981483498688980451328000000000000 951280259235695744887784594303169608024064 3026666683421937809266313265152000000000000))
theorem leaf00329_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1449451270981483498688980451328000000000000 951280259235695744887784594303169608024064 3026666683421937809266313265152000000000000 raw00329=true := by decide +kernel
#print axioms leaf00329_raw
theorem leaf00329_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00329=true := by decide +kernel
#print axioms leaf00329_rectangular
def affine00329 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00329 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00329_transform : affine00329=(NestedInteger.clearedAll 3 raw00329 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00329_transform
theorem leaf00329_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00329=true := by decide +kernel
#print axioms leaf00329_sign
theorem leaf00329_log : RationalLog.accepts (2144718689/4294967296) (-745644525/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00329_log
def leaf00329 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (157149821691/500000000000) (2144718689/4294967296) (-745644525/2147483648) 2 8 ![52,0,4] ![(9/80),0,(1/2)] ![(1/160),1,(1/2)] affine00329
theorem leaf00329_checked : FastNestedCellData.accepts 1 0 4 leaf00329=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (157149821691/500000000000) (2144718689/4294967296) (-745644525/2147483648) 2 8 ![52,0,4] ![(9/80),0,(1/2)] ![(1/160),1,(1/2)] 1449451270981483498688980451328000000000000 951280259235695744887784594303169608024064 3026666683421937809266313265152000000000000 raw00329 affine00329
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00329_raw leaf00329_rectangular
    leaf00329_transform leaf00329_sign leaf00329_log
#print axioms leaf00329_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
