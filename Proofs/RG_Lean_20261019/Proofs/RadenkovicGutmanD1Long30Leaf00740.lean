/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00740 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4049012470110774222291218726912000000000000 160060717332113684969633835272876027019264 182303654945219867958772236288000000000000))
theorem leaf00740_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4049012470110774222291218726912000000000000 160060717332113684969633835272876027019264 182303654945219867958772236288000000000000 raw00740=true := by decide +kernel
#print axioms leaf00740_raw
theorem leaf00740_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00740=true := by decide +kernel
#print axioms leaf00740_rectangular
def affine00740 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00740 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(209/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00740_transform : affine00740=(NestedInteger.clearedAll 3 raw00740 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(209/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00740_transform
theorem leaf00740_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00740=true := by decide +kernel
#print axioms leaf00740_sign
theorem leaf00740_log : RationalLog.accepts (45203527/2147483648) (-8291170275/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00740_log
def leaf00740 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (877989623303/1000000000000) (45203527/2147483648) (-8291170275/4294967296) 6 8 ![60,0,4] ![(209/6400),0,0] ![(3/6400),1,(1/16)] affine00740
theorem leaf00740_checked : FastNestedCellData.accepts 1 2 4 leaf00740=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (877989623303/1000000000000) (45203527/2147483648) (-8291170275/4294967296) 6 8 ![60,0,4] ![(209/6400),0,0] ![(3/6400),1,(1/16)] 4049012470110774222291218726912000000000000 160060717332113684969633835272876027019264 182303654945219867958772236288000000000000 raw00740 affine00740
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00740_raw leaf00740_rectangular
    leaf00740_transform leaf00740_sign leaf00740_log
#print axioms leaf00740_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
