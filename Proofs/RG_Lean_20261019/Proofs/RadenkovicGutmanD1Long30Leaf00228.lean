/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00228 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 13928039574373657526310797312000000000000 12807889921738264941990897097546854825984 353399620972223808882547359744000000000000))
theorem leaf00228_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 13928039574373657526310797312000000000000 12807889921738264941990897097546854825984 353399620972223808882547359744000000000000 raw00228=true := by decide +kernel
#print axioms leaf00228_raw
theorem leaf00228_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00228=true := by decide +kernel
#print axioms leaf00228_rectangular
def affine00228 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00228 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00228_transform : affine00228=(NestedInteger.clearedAll 3 raw00228 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00228_transform
theorem leaf00228_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00228=true := by decide +kernel
#print axioms leaf00228_sign
theorem leaf00228_log : RationalLog.accepts (3811415427/4294967296) (-256502607/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00228_log
def leaf00228 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9060486459/250000000000) (3811415427/4294967296) (-256502607/4294967296) 1 8 ![60,0,4] ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00228
theorem leaf00228_checked : FastNestedCellData.accepts 1 2 4 leaf00228=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9060486459/250000000000) (3811415427/4294967296) (-256502607/4294967296) 1 8 ![60,0,4] ![(151/32000),0,(1/4)] ![(3/32000),1,(1/4)] 13928039574373657526310797312000000000000 12807889921738264941990897097546854825984 353399620972223808882547359744000000000000 raw00228 affine00228
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00228_raw leaf00228_rectangular
    leaf00228_transform leaf00228_sign leaf00228_log
#print axioms leaf00228_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
