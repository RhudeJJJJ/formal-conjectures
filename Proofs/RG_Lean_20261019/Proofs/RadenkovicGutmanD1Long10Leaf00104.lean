/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00104 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 46356272204547681260903858176000000000000 42186267787652752201885516680723720830976 1049209805242201959542896459776000000000000))
theorem leaf00104_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 46356272204547681260903858176000000000000 42186267787652752201885516680723720830976 1049209805242201959542896459776000000000000 raw00104=true := by decide +kernel
#print axioms leaf00104_raw
theorem leaf00104_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00104=true := by decide +kernel
#print axioms leaf00104_rectangular
def affine00104 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00104 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00104_transform : affine00104=(NestedInteger.clearedAll 3 raw00104 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00104_transform
theorem leaf00104_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00104=true := by decide +kernel
#print axioms leaf00104_sign
theorem leaf00104_log : RationalLog.accepts (1878764823/2147483648) (-287080393/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00104_log
def leaf00104 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (20103828413/500000000000) (1878764823/2147483648) (-287080393/4294967296) 1 8 ![52,0,4] ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)] affine00104
theorem leaf00104_checked : FastNestedCellData.accepts 1 0 4 leaf00104=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (20103828413/500000000000) (1878764823/2147483648) (-287080393/4294967296) 1 8 ![52,0,4] ![(7/640),0,(1/2)] ![(1/3200),1,(1/2)] 46356272204547681260903858176000000000000 42186267787652752201885516680723720830976 1049209805242201959542896459776000000000000 raw00104 affine00104
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00104_raw leaf00104_rectangular
    leaf00104_transform leaf00104_sign leaf00104_log
#print axioms leaf00104_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
