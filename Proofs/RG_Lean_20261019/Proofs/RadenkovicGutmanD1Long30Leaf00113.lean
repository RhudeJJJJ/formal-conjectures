/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00113 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 14661354429459533877361193779200000000000 13986703679414816953707603386992485728256 703916256715138772334170813235200000000000))
theorem leaf00113_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 14661354429459533877361193779200000000000 13986703679414816953707603386992485728256 703916256715138772334170813235200000000000 raw00113=true := by decide +kernel
#print axioms leaf00113_raw
theorem leaf00113_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00113=true := by decide +kernel
#print axioms leaf00113_rectangular
def affine00113 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00113 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00113_transform : affine00113=(NestedInteger.clearedAll 3 raw00113 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00113_transform
theorem leaf00113_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00113=true := by decide +kernel
#print axioms leaf00113_sign
theorem leaf00113_log : RationalLog.accepts (4017504701/4294967296) (-71707667/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00113_log
def leaf00113 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3973968081/200000000000) (4017504701/4294967296) (-71707667/2147483648) 1 8 ![60,0,4] ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)] affine00113
theorem leaf00113_checked : FastNestedCellData.accepts 1 2 4 leaf00113=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3973968081/200000000000) (4017504701/4294967296) (-71707667/2147483648) 1 8 ![60,0,4] ![(41/16000),0,(1/4)] ![(3/32000),1,(1/4)] 14661354429459533877361193779200000000000 13986703679414816953707603386992485728256 703916256715138772334170813235200000000000 raw00113 affine00113
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00113_raw leaf00113_rectangular
    leaf00113_transform leaf00113_sign leaf00113_log
#print axioms leaf00113_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
