/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00062 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4501400412076051569369205964800000000000 4242792371110106005787216738089810526208 173869680239486187640081455513600000000000))
theorem leaf00062_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4501400412076051569369205964800000000000 4242792371110106005787216738089810526208 173869680239486187640081455513600000000000 raw00062=true := by decide +kernel
#print axioms leaf00062_raw
theorem leaf00062_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00062=true := by decide +kernel
#print axioms leaf00062_rectangular
def affine00062 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00062 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00062_transform : affine00062=(NestedInteger.clearedAll 3 raw00062 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00062_transform
theorem leaf00062_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00062=true := by decide +kernel
#print axioms leaf00062_sign
theorem leaf00062_log : RationalLog.accepts (3951786897/4294967296) (-44708517/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00062_log
def leaf00062 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2440214053/100000000000) (3951786897/4294967296) (-44708517/1073741824) 1 8 ![52,0,4] ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00062
theorem leaf00062_checked : FastNestedCellData.accepts 1 0 4 leaf00062=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2440214053/100000000000) (3951786897/4294967296) (-44708517/1073741824) 1 8 ![52,0,4] ![(21/3200),0,(1/2)] ![(1/3200),1,(1/2)] 4501400412076051569369205964800000000000 4242792371110106005787216738089810526208 173869680239486187640081455513600000000000 raw00062 affine00062
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00062_raw leaf00062_rectangular
    leaf00062_transform leaf00062_sign leaf00062_log
#print axioms leaf00062_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
