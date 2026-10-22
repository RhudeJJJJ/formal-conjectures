/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00364 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 13411825660028745242101499822080000000000 10973946672000615926576848752510477795328 24149861874837182752284957736960000000000))
theorem leaf00364_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 13411825660028745242101499822080000000000 10973946672000615926576848752510477795328 24149861874837182752284957736960000000000 raw00364=true := by decide +kernel
#print axioms leaf00364_raw
theorem leaf00364_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00364=true := by decide +kernel
#print axioms leaf00364_rectangular
def affine00364 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00364 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf00364_transform : affine00364=(NestedInteger.clearedAll 3 raw00364 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00364_transform
theorem leaf00364_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00364=true := by decide +kernel
#print axioms leaf00364_sign
theorem leaf00364_log : RationalLog.accepts (2416283327/4294967296) (-1235261399/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00364_log
def leaf00364 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (18176413147/40000000000) (2416283327/4294967296) (-1235261399/4294967296) 1 8 ![52,0,4] ![(19/80),0,(1/4)] ![(3/160),1,(1/4)] affine00364
theorem leaf00364_checked : FastNestedCellData.accepts 1 0 4 leaf00364=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (18176413147/40000000000) (2416283327/4294967296) (-1235261399/4294967296) 1 8 ![52,0,4] ![(19/80),0,(1/4)] ![(3/160),1,(1/4)] 13411825660028745242101499822080000000000 10973946672000615926576848752510477795328 24149861874837182752284957736960000000000 raw00364 affine00364
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00364_raw leaf00364_rectangular
    leaf00364_transform leaf00364_sign leaf00364_log
#print axioms leaf00364_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
