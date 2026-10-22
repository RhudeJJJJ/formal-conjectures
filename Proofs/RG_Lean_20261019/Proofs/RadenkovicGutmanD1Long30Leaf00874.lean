/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00874 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9203273081555651146143707955200000000000 6372632188121636676840097106364028944384 31932746645797955685346757836800000000000))
theorem leaf00874_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9203273081555651146143707955200000000000 6372632188121636676840097106364028944384 31932746645797955685346757836800000000000 raw00874=true := by decide +kernel
#print axioms leaf00874_raw
theorem leaf00874_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00874=true := by decide +kernel
#print axioms leaf00874_rectangular
def affine00874 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00874 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00874_transform : affine00874=(NestedInteger.clearedAll 3 raw00874 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00874_transform
theorem leaf00874_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00874=true := by decide +kernel
#print axioms leaf00874_sign
theorem leaf00874_log : RationalLog.accepts (2479207739/4294967296) (-590026403/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00874_log
def leaf00874 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9978208669/50000000000) (2479207739/4294967296) (-590026403/2147483648) 1 8 ![60,0,4] ![(19/320),0,(1/2)] ![(1/640),1,(1/2)] affine00874
theorem leaf00874_checked : FastNestedCellData.accepts 1 2 4 leaf00874=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9978208669/50000000000) (2479207739/4294967296) (-590026403/2147483648) 1 8 ![60,0,4] ![(19/320),0,(1/2)] ![(1/640),1,(1/2)] 9203273081555651146143707955200000000000 6372632188121636676840097106364028944384 31932746645797955685346757836800000000000 raw00874 affine00874
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00874_raw leaf00874_rectangular
    leaf00874_transform leaf00874_sign leaf00874_log
#print axioms leaf00874_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
