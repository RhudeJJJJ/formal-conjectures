/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00313 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 33046524209698563459119054848000000000000 17149754567564507666352246343368014036992 37394857160711239358369234944000000000000))
theorem leaf00313_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 33046524209698563459119054848000000000000 17149754567564507666352246343368014036992 37394857160711239358369234944000000000000 raw00313=true := by decide +kernel
#print axioms leaf00313_raw
theorem leaf00313_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00313=true := by decide +kernel
#print axioms leaf00313_rectangular
def affine00313 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00313 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00313_transform : affine00313=(NestedInteger.clearedAll 3 raw00313 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00313_transform
theorem leaf00313_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00313=true := by decide +kernel
#print axioms leaf00313_sign
theorem leaf00313_log : RationalLog.accepts (1528100813/4294967296) (-2219248919/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00313_log
def leaf00313 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (28663290673/62500000000) (1528100813/4294967296) (-2219248919/4294967296) 2 8 ![52,0,4] ![(3/32),0,(1/4)] ![(1/320),1,(1/4)] affine00313
theorem leaf00313_checked : FastNestedCellData.accepts 1 0 4 leaf00313=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (28663290673/62500000000) (1528100813/4294967296) (-2219248919/4294967296) 2 8 ![52,0,4] ![(3/32),0,(1/4)] ![(1/320),1,(1/4)] 33046524209698563459119054848000000000000 17149754567564507666352246343368014036992 37394857160711239358369234944000000000000 raw00313 affine00313
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00313_raw leaf00313_rectangular
    leaf00313_transform leaf00313_sign leaf00313_log
#print axioms leaf00313_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
