/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00042 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2068899509025831498566779011072000000000000 285609321529390109986190970693837914112 2546552907153646380684148736000000000000))
theorem leaf00042_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2068899509025831498566779011072000000000000 285609321529390109986190970693837914112 2546552907153646380684148736000000000000 raw00042=true := by decide +kernel
#print axioms leaf00042_raw
theorem leaf00042_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00042=true := by decide +kernel
#print axioms leaf00042_rectangular
def affine00042 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00042 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/8000),0,0] ![(3/8000),1,(1/4)]))
theorem leaf00042_transform : affine00042=(NestedInteger.clearedAll 3 raw00042 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/8000),0,0] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00042_transform
theorem leaf00042_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00042=true := by decide +kernel
#print axioms leaf00042_sign
theorem leaf00042_log : RationalLog.accepts (533123/4294967296) (-9657451447/2147483648) 13 8=true := by decide +kernel
#print axioms leaf00042_log
def leaf00042 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (112155267117/1000000000000) (533123/4294967296) (-9657451447/2147483648) 13 8 ![52,0,4] ![(37/8000),0,0] ![(3/8000),1,(1/4)] affine00042
theorem leaf00042_checked : FastNestedCellData.accepts 1 0 4 leaf00042=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (112155267117/1000000000000) (533123/4294967296) (-9657451447/2147483648) 13 8 ![52,0,4] ![(37/8000),0,0] ![(3/8000),1,(1/4)] 2068899509025831498566779011072000000000000 285609321529390109986190970693837914112 2546552907153646380684148736000000000000 raw00042 affine00042
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00042_raw leaf00042_rectangular
    leaf00042_transform leaf00042_sign leaf00042_log
#print axioms leaf00042_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
