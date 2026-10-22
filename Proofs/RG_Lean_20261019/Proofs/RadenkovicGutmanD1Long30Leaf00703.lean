/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00703 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 191671852455892761076521605529600000000000 125033147521680163069048533455485708271616 601667496690356112552695431168000000000000))
theorem leaf00703_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 191671852455892761076521605529600000000000 125033147521680163069048533455485708271616 601667496690356112552695431168000000000000 raw00703=true := by decide +kernel
#print axioms leaf00703_raw
theorem leaf00703_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00703=true := by decide +kernel
#print axioms leaf00703_rectangular
def affine00703 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00703 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00703_transform : affine00703=(NestedInteger.clearedAll 3 raw00703 (IntegerComputedClassCell.leftNumerator ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00703_transform
theorem leaf00703_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00703=true := by decide +kernel
#print axioms leaf00703_sign
theorem leaf00703_log : RationalLog.accepts (1159838965/2147483648) (-661441719/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00703_log
def leaf00703 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (207811038837/1000000000000) (1159838965/2147483648) (-661441719/2147483648) 1 8 ![60,0,4] ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)] affine00703
theorem leaf00703_checked : FastNestedCellData.accepts 1 2 4 leaf00703=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (207811038837/1000000000000) (1159838965/2147483648) (-661441719/2147483648) 1 8 ![60,0,4] ![(37/1280),0,(1/4)] ![(3/6400),1,(1/4)] 191671852455892761076521605529600000000000 125033147521680163069048533455485708271616 601667496690356112552695431168000000000000 raw00703 affine00703
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00703_raw leaf00703_rectangular
    leaf00703_transform leaf00703_sign leaf00703_log
#print axioms leaf00703_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
