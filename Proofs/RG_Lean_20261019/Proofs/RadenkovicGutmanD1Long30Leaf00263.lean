/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00263 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12490948059487552227631955968000000000000 11295683218726437733807400144071062192128 260649472523518637664081281024000000000000))
theorem leaf00263_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12490948059487552227631955968000000000000 11295683218726437733807400144071062192128 260649472523518637664081281024000000000000 raw00263=true := by decide +kernel
#print axioms leaf00263_raw
theorem leaf00263_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00263=true := by decide +kernel
#print axioms leaf00263_rectangular
def affine00263 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00263 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00263_transform : affine00263=(NestedInteger.clearedAll 3 raw00263 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00263_transform
theorem leaf00263_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00263=true := by decide +kernel
#print axioms leaf00263_sign
theorem leaf00263_log : RationalLog.accepts (3722652403/4294967296) (-9597073/134217728) 1 8=true := by decide +kernel
#print axioms leaf00263_log
def leaf00263 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (5417085209/125000000000) (3722652403/4294967296) (-9597073/134217728) 1 8 ![60,0,4] ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)] affine00263
theorem leaf00263_checked : FastNestedCellData.accepts 1 2 4 leaf00263=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (5417085209/125000000000) (3722652403/4294967296) (-9597073/134217728) 1 8 ![60,0,4] ![(9/1600),0,(1/4)] ![(1/6400),1,(1/4)] 12490948059487552227631955968000000000000 11295683218726437733807400144071062192128 260649472523518637664081281024000000000000 raw00263 affine00263
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00263_raw leaf00263_rectangular
    leaf00263_transform leaf00263_sign leaf00263_log
#print axioms leaf00263_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
