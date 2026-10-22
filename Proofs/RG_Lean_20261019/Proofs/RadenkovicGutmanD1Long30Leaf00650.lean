/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00650 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 247409209214932039364954292224000000000000 5366468433676720146036085951488143130624 6251906386803869558866182144000000000000))
theorem leaf00650_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 247409209214932039364954292224000000000000 5366468433676720146036085951488143130624 6251906386803869558866182144000000000000 raw00650=true := by decide +kernel
#print axioms leaf00650_raw
theorem leaf00650_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00650=true := by decide +kernel
#print axioms leaf00650_rectangular
def affine00650 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00650 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1280),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00650_transform : affine00650=(NestedInteger.clearedAll 3 raw00650 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1280),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00650_transform
theorem leaf00650_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00650=true := by decide +kernel
#print axioms leaf00650_sign
theorem leaf00650_log : RationalLog.accepts (25065113/2147483648) (-9557537457/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00650_log
def leaf00650 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (214593281699/250000000000) (25065113/2147483648) (-9557537457/4294967296) 7 8 ![60,0,4] ![(31/1280),0,0] ![(3/6400),1,(1/16)] affine00650
theorem leaf00650_checked : FastNestedCellData.accepts 1 2 4 leaf00650=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (214593281699/250000000000) (25065113/2147483648) (-9557537457/4294967296) 7 8 ![60,0,4] ![(31/1280),0,0] ![(3/6400),1,(1/16)] 247409209214932039364954292224000000000000 5366468433676720146036085951488143130624 6251906386803869558866182144000000000000 raw00650 affine00650
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00650_raw leaf00650_rectangular
    leaf00650_transform leaf00650_sign leaf00650_log
#print axioms leaf00650_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
