/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00538 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2173795797823408623027520274432000000000000 1676932552844054937470592850568842026418176 14230382477581577674218471948288000000000000))
theorem leaf00538_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2173795797823408623027520274432000000000000 1676932552844054937470592850568842026418176 14230382477581577674218471948288000000000000 raw00538=true := by decide +kernel
#print axioms leaf00538_raw
theorem leaf00538_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00538=true := by decide +kernel
#print axioms leaf00538_rectangular
def affine00538 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00538 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00538_transform : affine00538=(NestedInteger.clearedAll 3 raw00538 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00538_transform
theorem leaf00538_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00538=true := by decide +kernel
#print axioms leaf00538_sign
theorem leaf00538_log : RationalLog.accepts (2963987739/4294967296) (-49782481/268435456) 1 8=true := by decide +kernel
#print axioms leaf00538_log
def leaf00538 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (117841706327/1000000000000) (2963987739/4294967296) (-49782481/268435456) 1 8 ![60,0,4] ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)] affine00538
theorem leaf00538_checked : FastNestedCellData.accepts 1 2 4 leaf00538=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (117841706327/1000000000000) (2963987739/4294967296) (-49782481/268435456) 1 8 ![60,0,4] ![(1/64),0,(1/4)] ![(1/3200),1,(1/4)] 2173795797823408623027520274432000000000000 1676932552844054937470592850568842026418176 14230382477581577674218471948288000000000000 raw00538 affine00538
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00538_raw leaf00538_rectangular
    leaf00538_transform leaf00538_sign leaf00538_log
#print axioms leaf00538_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
