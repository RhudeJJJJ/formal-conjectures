/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01204 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6227333763334871686511067136000000000000 7224592744521548479560962352880048668672 445850966814885390929870454784000000000000))
theorem leaf01204_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6227333763334871686511067136000000000000 7224592744521548479560962352880048668672 445850966814885390929870454784000000000000 raw01204=true := by decide +kernel
#print axioms leaf01204_raw
theorem leaf01204_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01204=true := by decide +kernel
#print axioms leaf01204_rectangular
def affine01204 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01204 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/64),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01204_transform : affine01204=(NestedInteger.clearedAll 3 raw01204 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/64),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01204_transform
theorem leaf01204_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01204=true := by decide +kernel
#print axioms leaf01204_sign
theorem leaf01204_log : RationalLog.accepts (4903319199/4294967296) (142236885/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01204_log
def leaf01204 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4051013277/250000000000) (4903319199/4294967296) (142236885/2147483648) 0 8 ![60,0,4] ![(23/64),0,(15/16)] ![(1/64),1,(1/16)] affine01204
theorem leaf01204_checked : FastNestedCellData.accepts 1 2 4 leaf01204=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4051013277/250000000000) (4903319199/4294967296) (142236885/2147483648) 0 8 ![60,0,4] ![(23/64),0,(15/16)] ![(1/64),1,(1/16)] 6227333763334871686511067136000000000000 7224592744521548479560962352880048668672 445850966814885390929870454784000000000000 raw01204 affine01204
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01204_raw leaf01204_rectangular
    leaf01204_transform leaf01204_sign leaf01204_log
#print axioms leaf01204_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
