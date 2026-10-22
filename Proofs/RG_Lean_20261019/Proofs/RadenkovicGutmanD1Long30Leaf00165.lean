/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00165 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1502748788447740538200373854208000000000000 386313460165467497423753715076860739584 1185531738019662609034248192000000000000))
theorem leaf00165_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1502748788447740538200373854208000000000000 386313460165467497423753715076860739584 1185531738019662609034248192000000000000 raw00165=true := by decide +kernel
#print axioms leaf00165_raw
theorem leaf00165_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00165=true := by decide +kernel
#print axioms leaf00165_rectangular
def affine00165 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00165 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/6400),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00165_transform : affine00165=(NestedInteger.clearedAll 3 raw00165 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/6400),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00165_transform
theorem leaf00165_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00165=true := by decide +kernel
#print axioms leaf00165_sign
theorem leaf00165_log : RationalLog.accepts (416377/2147483648) (-18357155007/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00165_log
def leaf00165 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (325856700227/1000000000000) (416377/2147483648) (-18357155007/4294967296) 13 8 ![60,0,4] ![(23/6400),0,0] ![(3/32000),1,(1/16)] affine00165
theorem leaf00165_checked : FastNestedCellData.accepts 1 2 4 leaf00165=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (325856700227/1000000000000) (416377/2147483648) (-18357155007/4294967296) 13 8 ![60,0,4] ![(23/6400),0,0] ![(3/32000),1,(1/16)] 1502748788447740538200373854208000000000000 386313460165467497423753715076860739584 1185531738019662609034248192000000000000 raw00165 affine00165
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00165_raw leaf00165_rectangular
    leaf00165_transform leaf00165_sign leaf00165_log
#print axioms leaf00165_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
