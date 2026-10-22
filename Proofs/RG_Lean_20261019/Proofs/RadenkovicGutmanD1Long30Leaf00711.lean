/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00711 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4577827844065086676088693719040000000000 1246624346655802702076365242957350043648 2009351252352425964231909703680000000000))
theorem leaf00711_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4577827844065086676088693719040000000000 1246624346655802702076365242957350043648 2009351252352425964231909703680000000000 raw00711=true := by decide +kernel
#print axioms leaf00711_raw
theorem leaf00711_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00711=true := by decide +kernel
#print axioms leaf00711_rectangular
def affine00711 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00711 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00711_transform : affine00711=(NestedInteger.clearedAll 3 raw00711 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00711_transform
theorem leaf00711_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00711=true := by decide +kernel
#print axioms leaf00711_sign
theorem leaf00711_log : RationalLog.accepts (360894891/2147483648) (-3829962641/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00711_log
def leaf00711 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (24816454469/40000000000) (360894891/2147483648) (-3829962641/4294967296) 3 8 ![60,0,4] ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00711
theorem leaf00711_checked : FastNestedCellData.accepts 1 2 4 leaf00711=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (24816454469/40000000000) (360894891/2147483648) (-3829962641/4294967296) 3 8 ![60,0,4] ![(191/6400),0,(1/16)] ![(3/6400),1,(1/16)] 4577827844065086676088693719040000000000 1246624346655802702076365242957350043648 2009351252352425964231909703680000000000 raw00711 affine00711
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00711_raw leaf00711_rectangular
    leaf00711_transform leaf00711_sign leaf00711_log
#print axioms leaf00711_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
