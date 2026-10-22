/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00733 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 41508456174580934595689893068800000000000 26321218039530798283859317837169669701632 116973941608762727960498562662400000000000))
theorem leaf00733_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 41508456174580934595689893068800000000000 26321218039530798283859317837169669701632 116973941608762727960498562662400000000000 raw00733=true := by decide +kernel
#print axioms leaf00733_raw
theorem leaf00733_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00733=true := by decide +kernel
#print axioms leaf00733_rectangular
def affine00733 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00733 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00733_transform : affine00733=(NestedInteger.clearedAll 3 raw00733 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00733_transform
theorem leaf00733_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00733=true := by decide +kernel
#print axioms leaf00733_sign
theorem leaf00733_log : RationalLog.accepts (1111621329/2147483648) (-1414068957/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00733_log
def leaf00733 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (45003558361/200000000000) (1111621329/2147483648) (-1414068957/4294967296) 1 8 ![60,0,4] ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00733
theorem leaf00733_checked : FastNestedCellData.accepts 1 2 4 leaf00733=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (45003558361/200000000000) (1111621329/2147483648) (-1414068957/4294967296) 1 8 ![60,0,4] ![(203/6400),0,(1/4)] ![(3/6400),1,(1/4)] 41508456174580934595689893068800000000000 26321218039530798283859317837169669701632 116973941608762727960498562662400000000000 raw00733 affine00733
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00733_raw leaf00733_rectangular
    leaf00733_transform leaf00733_sign leaf00733_log
#print axioms leaf00733_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
