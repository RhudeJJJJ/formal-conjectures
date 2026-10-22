/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00144 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 33745392009546225620405452800000000000 32816410719592741832385030101535817728 2802956446018323326492370534400000000000))
theorem leaf00144_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 33745392009546225620405452800000000000 32816410719592741832385030101535817728 2802956446018323326492370534400000000000 raw00144=true := by decide +kernel
#print axioms leaf00144_raw
theorem leaf00144_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00144=true := by decide +kernel
#print axioms leaf00144_rectangular
def affine00144 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00144 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00144_transform : affine00144=(NestedInteger.clearedAll 3 raw00144 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00144_transform
theorem leaf00144_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00144=true := by decide +kernel
#print axioms leaf00144_sign
theorem leaf00144_log : RationalLog.accepts (258024763/268435456) (-84943617/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00144_log
def leaf00144 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2341556949/200000000000) (258024763/268435456) (-84943617/4294967296) 1 8 ![60,0,4] ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)] affine00144
theorem leaf00144_checked : FastNestedCellData.accepts 1 2 4 leaf00144=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2341556949/200000000000) (258024763/268435456) (-84943617/4294967296) 1 8 ![60,0,4] ![(1/320),0,(1/2)] ![(3/32000),1,(1/2)] 33745392009546225620405452800000000000 32816410719592741832385030101535817728 2802956446018323326492370534400000000000 raw00144 affine00144
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00144_raw leaf00144_rectangular
    leaf00144_transform leaf00144_sign leaf00144_log
#print axioms leaf00144_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
