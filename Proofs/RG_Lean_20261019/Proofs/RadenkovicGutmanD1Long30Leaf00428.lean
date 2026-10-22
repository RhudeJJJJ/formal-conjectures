/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00428 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 721205507001927984073408512000000000000 600149416377510038288472793791288311808 7323670522587596377569624064000000000000))
theorem leaf00428_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 721205507001927984073408512000000000000 600149416377510038288472793791288311808 7323670522587596377569624064000000000000 raw00428=true := by decide +kernel
#print axioms leaf00428_raw
theorem leaf00428_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00428=true := by decide +kernel
#print axioms leaf00428_rectangular
def affine00428 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00428 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00428_transform : affine00428=(NestedInteger.clearedAll 3 raw00428 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00428_transform
theorem leaf00428_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00428=true := by decide +kernel
#print axioms leaf00428_sign
theorem leaf00428_log : RationalLog.accepts (1651674331/2147483648) (-563730043/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00428_log
def leaf00428 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40973267061/500000000000) (1651674331/2147483648) (-563730043/4294967296) 1 8 ![60,0,4] ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00428
theorem leaf00428_checked : FastNestedCellData.accepts 1 2 4 leaf00428=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40973267061/500000000000) (1651674331/2147483648) (-563730043/4294967296) 1 8 ![60,0,4] ![(69/6400),0,(1/4)] ![(1/6400),1,(1/4)] 721205507001927984073408512000000000000 600149416377510038288472793791288311808 7323670522587596377569624064000000000000 raw00428 affine00428
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00428_raw leaf00428_rectangular
    leaf00428_transform leaf00428_sign leaf00428_log
#print axioms leaf00428_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
