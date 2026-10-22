/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01096 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 258938631899857645808880975872000000000000 296074912295840889177281193294257939546112 1318270398109138991737152208896000000000000))
theorem leaf01096_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 258938631899857645808880975872000000000000 296074912295840889177281193294257939546112 1318270398109138991737152208896000000000000 raw01096=true := by decide +kernel
#print axioms leaf01096_raw
theorem leaf01096_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01096=true := by decide +kernel
#print axioms leaf01096_rectangular
def affine01096 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01096 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01096_transform : affine01096=(NestedInteger.clearedAll 3 raw01096 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01096_transform
theorem leaf01096_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01096=true := by decide +kernel
#print axioms leaf01096_sign
theorem leaf01096_log : RationalLog.accepts (1002565357/1073741824) (-36822647/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01096_log
def leaf01096 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (224593461797/1000000000000) (1002565357/1073741824) (-36822647/1073741824) 1 8 ![60,0,4] ![(1/2),0,(1/2)] ![(1/32),1,(1/4)] affine01096
theorem leaf01096_checked : FastNestedCellData.accepts 1 2 4 leaf01096=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (224593461797/1000000000000) (1002565357/1073741824) (-36822647/1073741824) 1 8 ![60,0,4] ![(1/2),0,(1/2)] ![(1/32),1,(1/4)] 258938631899857645808880975872000000000000 296074912295840889177281193294257939546112 1318270398109138991737152208896000000000000 raw01096 affine01096
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01096_raw leaf01096_rectangular
    leaf01096_transform leaf01096_sign leaf01096_log
#print axioms leaf01096_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
