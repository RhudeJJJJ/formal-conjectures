/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00289 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 230988174322924356918677864448000000000 118223816878415711975033720964202364928 295042768391412109822394368000000000000))
theorem leaf00289_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 230988174322924356918677864448000000000 118223816878415711975033720964202364928 295042768391412109822394368000000000000 raw00289=true := by decide +kernel
#print axioms leaf00289_raw
theorem leaf00289_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00289=true := by decide +kernel
#print axioms leaf00289_rectangular
def affine00289 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00289 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00289_transform : affine00289=(NestedInteger.clearedAll 3 raw00289 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00289_transform
theorem leaf00289_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00289=true := by decide +kernel
#print axioms leaf00289_sign
theorem leaf00289_log : RationalLog.accepts (98086625/268435456) (-1080999797/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00289_log
def leaf00289 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (400700608671/1000000000000) (98086625/268435456) (-1080999797/2147483648) 2 8 ![52,0,4] ![(11/160),0,(1/4)] ![(1/320),1,(1/4)] affine00289
theorem leaf00289_checked : FastNestedCellData.accepts 1 0 4 leaf00289=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (400700608671/1000000000000) (98086625/268435456) (-1080999797/2147483648) 2 8 ![52,0,4] ![(11/160),0,(1/4)] ![(1/320),1,(1/4)] 230988174322924356918677864448000000000 118223816878415711975033720964202364928 295042768391412109822394368000000000000 raw00289 affine00289
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00289_raw leaf00289_rectangular
    leaf00289_transform leaf00289_sign leaf00289_log
#print axioms leaf00289_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
