/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00284 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 63871687751784002503335099760640000000 43293064911496084986675959913328410624 200055108408575200318822809600000000000))
theorem leaf00284_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 63871687751784002503335099760640000000 43293064911496084986675959913328410624 200055108408575200318822809600000000000 raw00284=true := by decide +kernel
#print axioms leaf00284_raw
theorem leaf00284_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00284=true := by decide +kernel
#print axioms leaf00284_rectangular
def affine00284 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00284 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00284_transform : affine00284=(NestedInteger.clearedAll 3 raw00284 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00284_transform
theorem leaf00284_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00284=true := by decide +kernel
#print axioms leaf00284_sign
theorem leaf00284_log : RationalLog.accepts (2393268125/4294967296) (-1255814313/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00284_log
def leaf00284 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (21640569569/100000000000) (2393268125/4294967296) (-1255814313/4294967296) 1 8 ![52,0,4] ![(21/320),0,(1/2)] ![(1/640),1,(1/2)] affine00284
theorem leaf00284_checked : FastNestedCellData.accepts 1 0 4 leaf00284=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (21640569569/100000000000) (2393268125/4294967296) (-1255814313/4294967296) 1 8 ![52,0,4] ![(21/320),0,(1/2)] ![(1/640),1,(1/2)] 63871687751784002503335099760640000000 43293064911496084986675959913328410624 200055108408575200318822809600000000000 raw00284 affine00284
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00284_raw leaf00284_rectangular
    leaf00284_transform leaf00284_sign leaf00284_log
#print axioms leaf00284_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
