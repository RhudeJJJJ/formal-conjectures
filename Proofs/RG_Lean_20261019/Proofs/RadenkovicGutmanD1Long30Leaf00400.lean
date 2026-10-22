/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00400 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12351204603954100360764651995136000000000000 40052974667461065557851767191607428775936 59819831083106873176716476416000000000000))
theorem leaf00400_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12351204603954100360764651995136000000000000 40052974667461065557851767191607428775936 59819831083106873176716476416000000000000 raw00400=true := by decide +kernel
#print axioms leaf00400_raw
theorem leaf00400_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00400=true := by decide +kernel
#print axioms leaf00400_rectangular
def affine00400 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00400 (IntegerComputedClassCell.leftNumerator ![(1/100),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/100),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00400_transform : affine00400=(NestedInteger.clearedAll 3 raw00400 (IntegerComputedClassCell.leftNumerator ![(1/100),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/100),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00400_transform
theorem leaf00400_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00400=true := by decide +kernel
#print axioms leaf00400_sign
theorem leaf00400_log : RationalLog.accepts (8342251/4294967296) (-6704300391/2147483648) 10 8=true := by decide +kernel
#print axioms leaf00400_log
def leaf00400 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (669560143221/1000000000000) (8342251/4294967296) (-6704300391/2147483648) 10 8 ![60,0,4] ![(1/100),0,0] ![(1/6400),1,(1/16)] affine00400
theorem leaf00400_checked : FastNestedCellData.accepts 1 2 4 leaf00400=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (669560143221/1000000000000) (8342251/4294967296) (-6704300391/2147483648) 10 8 ![60,0,4] ![(1/100),0,0] ![(1/6400),1,(1/16)] 12351204603954100360764651995136000000000000 40052974667461065557851767191607428775936 59819831083106873176716476416000000000000 raw00400 affine00400
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00400_raw leaf00400_rectangular
    leaf00400_transform leaf00400_sign leaf00400_log
#print axioms leaf00400_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
