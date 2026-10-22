/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00694 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5855241558819948813945195724800000000000 4711624351408237775447421585825931984896 46386925131937886471639269376000000000000))
theorem leaf00694_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5855241558819948813945195724800000000000 4711624351408237775447421585825931984896 46386925131937886471639269376000000000000 raw00694=true := by decide +kernel
#print axioms leaf00694_raw
theorem leaf00694_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00694=true := by decide +kernel
#print axioms leaf00694_rectangular
def affine00694 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00694 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00694_transform : affine00694=(NestedInteger.clearedAll 3 raw00694 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00694_transform
theorem leaf00694_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00694=true := by decide +kernel
#print axioms leaf00694_sign
theorem leaf00694_log : RationalLog.accepts (3137420395/4294967296) (-337201131/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00694_log
def leaf00694 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12696531237/125000000000) (3137420395/4294967296) (-337201131/2147483648) 1 8 ![60,0,4] ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00694
theorem leaf00694_checked : FastNestedCellData.accepts 1 2 4 leaf00694=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12696531237/125000000000) (3137420395/4294967296) (-337201131/2147483648) 1 8 ![60,0,4] ![(179/6400),0,(1/2)] ![(3/6400),1,(1/2)] 5855241558819948813945195724800000000000 4711624351408237775447421585825931984896 46386925131937886471639269376000000000000 raw00694 affine00694
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00694_raw leaf00694_rectangular
    leaf00694_transform leaf00694_sign leaf00694_log
#print axioms leaf00694_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
