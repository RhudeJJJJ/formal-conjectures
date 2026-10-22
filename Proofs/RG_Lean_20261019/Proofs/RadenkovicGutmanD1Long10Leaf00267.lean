/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00267 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1049506363085813857973715337216000000000000 87456688342760327372283527497416676737024 128099203280800329134927511552000000000000))
theorem leaf00267_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1049506363085813857973715337216000000000000 87456688342760327372283527497416676737024 128099203280800329134927511552000000000000 raw00267=true := by decide +kernel
#print axioms leaf00267_raw
theorem leaf00267_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00267=true := by decide +kernel
#print axioms leaf00267_rectangular
def affine00267 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00267 (IntegerComputedClassCell.leftNumerator ![(37/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/640),0,0] ![(1/640),1,(1/4)]))
theorem leaf00267_transform : affine00267=(NestedInteger.clearedAll 3 raw00267 (IntegerComputedClassCell.leftNumerator ![(37/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/640),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00267_transform
theorem leaf00267_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00267=true := by decide +kernel
#print axioms leaf00267_sign
theorem leaf00267_log : RationalLog.accepts (106346781/2147483648) (-3226966607/2147483648) 5 8=true := by decide +kernel
#print axioms leaf00267_log
def leaf00267 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (682726247337/1000000000000) (106346781/2147483648) (-3226966607/2147483648) 5 8 ![52,0,4] ![(37/640),0,0] ![(1/640),1,(1/4)] affine00267
theorem leaf00267_checked : FastNestedCellData.accepts 1 0 4 leaf00267=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (682726247337/1000000000000) (106346781/2147483648) (-3226966607/2147483648) 5 8 ![52,0,4] ![(37/640),0,0] ![(1/640),1,(1/4)] 1049506363085813857973715337216000000000000 87456688342760327372283527497416676737024 128099203280800329134927511552000000000000 raw00267 affine00267
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00267_raw leaf00267_rectangular
    leaf00267_transform leaf00267_sign leaf00267_log
#print axioms leaf00267_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
