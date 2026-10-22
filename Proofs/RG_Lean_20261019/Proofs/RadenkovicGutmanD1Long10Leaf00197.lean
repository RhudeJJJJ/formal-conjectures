/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00197 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 129490088731008360091236696064000000000000 101693645270137263523808944979968469762048 905434475045854092597219295232000000000000))
theorem leaf00197_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 129490088731008360091236696064000000000000 101693645270137263523808944979968469762048 905434475045854092597219295232000000000000 raw00197=true := by decide +kernel
#print axioms leaf00197_raw
theorem leaf00197_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00197=true := by decide +kernel
#print axioms leaf00197_rectangular
def affine00197 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00197 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00197_transform : affine00197=(NestedInteger.clearedAll 3 raw00197 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00197_transform
theorem leaf00197_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00197=true := by decide +kernel
#print axioms leaf00197_sign
theorem leaf00197_log : RationalLog.accepts (1516210349/2147483648) (-747502007/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00197_log
def leaf00197 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (56157374207/500000000000) (1516210349/2147483648) (-747502007/4294967296) 1 8 ![52,0,4] ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)] affine00197
theorem leaf00197_checked : FastNestedCellData.accepts 1 0 4 leaf00197=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (56157374207/500000000000) (1516210349/2147483648) (-747502007/4294967296) 1 8 ![52,0,4] ![(1/32),0,(1/2)] ![(3/3200),1,(1/2)] 129490088731008360091236696064000000000000 101693645270137263523808944979968469762048 905434475045854092597219295232000000000000 raw00197 affine00197
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00197_raw leaf00197_rectangular
    leaf00197_transform leaf00197_sign leaf00197_log
#print axioms leaf00197_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
