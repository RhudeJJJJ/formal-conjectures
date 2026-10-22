/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00223 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 40965104675248021953407090688000000000000 37730107912604099751625921624925464952832 1061875787415276575905823064064000000000000))
theorem leaf00223_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 40965104675248021953407090688000000000000 37730107912604099751625921624925464952832 1061875787415276575905823064064000000000000 raw00223=true := by decide +kernel
#print axioms leaf00223_raw
theorem leaf00223_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00223=true := by decide +kernel
#print axioms leaf00223_rectangular
def affine00223 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00223 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00223_transform : affine00223=(NestedInteger.clearedAll 3 raw00223 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00223_transform
theorem leaf00223_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00223=true := by decide +kernel
#print axioms leaf00223_sign
theorem leaf00223_log : RationalLog.accepts (3820062763/4294967296) (-251635917/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00223_log
def leaf00223 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8882891097/250000000000) (3820062763/4294967296) (-251635917/4294967296) 1 8 ![60,0,4] ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)] affine00223
theorem leaf00223_checked : FastNestedCellData.accepts 1 2 4 leaf00223=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8882891097/250000000000) (3820062763/4294967296) (-251635917/4294967296) 1 8 ![60,0,4] ![(37/8000),0,(1/4)] ![(3/32000),1,(1/4)] 40965104675248021953407090688000000000000 37730107912604099751625921624925464952832 1061875787415276575905823064064000000000000 raw00223 affine00223
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00223_raw leaf00223_rectangular
    leaf00223_transform leaf00223_sign leaf00223_log
#print axioms leaf00223_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
