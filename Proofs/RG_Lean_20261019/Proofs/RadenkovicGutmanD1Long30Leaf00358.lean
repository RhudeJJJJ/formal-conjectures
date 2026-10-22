/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00358 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 75708333786194691607282843648000000000000 65217567483633034385568649312551317798912 993163265782236805294135967744000000000000))
theorem leaf00358_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 75708333786194691607282843648000000000000 65217567483633034385568649312551317798912 993163265782236805294135967744000000000000 raw00358=true := by decide +kernel
#print axioms leaf00358_raw
theorem leaf00358_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00358=true := by decide +kernel
#print axioms leaf00358_rectangular
def affine00358 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00358 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00358_transform : affine00358=(NestedInteger.clearedAll 3 raw00358 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00358_transform
theorem leaf00358_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00358=true := by decide +kernel
#print axioms leaf00358_sign
theorem leaf00358_log : RationalLog.accepts (867959497/1073741824) (-114224561/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00358_log
def leaf00358 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (65666511973/1000000000000) (867959497/1073741824) (-114224561/1073741824) 1 8 ![60,0,4] ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)] affine00358
theorem leaf00358_checked : FastNestedCellData.accepts 1 2 4 leaf00358=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (65666511973/1000000000000) (867959497/1073741824) (-114224561/1073741824) 1 8 ![60,0,4] ![(11/1280),0,(1/4)] ![(1/6400),1,(1/4)] 75708333786194691607282843648000000000000 65217567483633034385568649312551317798912 993163265782236805294135967744000000000000 raw00358 affine00358
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00358_raw leaf00358_rectangular
    leaf00358_transform leaf00358_sign leaf00358_log
#print axioms leaf00358_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
