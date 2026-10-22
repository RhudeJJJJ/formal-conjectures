/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00309 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 19337941333889288443355704852480000000000 18189724392667494359304386733337439371264 694057727964705552366674378752000000000000))
theorem leaf00309_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 19337941333889288443355704852480000000000 18189724392667494359304386733337439371264 694057727964705552366674378752000000000000 raw00309=true := by decide +kernel
#print axioms leaf00309_raw
theorem leaf00309_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00309=true := by decide +kernel
#print axioms leaf00309_rectangular
def affine00309 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00309 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00309_transform : affine00309=(NestedInteger.clearedAll 3 raw00309 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00309_transform
theorem leaf00309_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00309=true := by decide +kernel
#print axioms leaf00309_sign
theorem leaf00309_log : RationalLog.accepts (3936773525/4294967296) (-187008185/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00309_log
def leaf00309 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (26207797507/1000000000000) (3936773525/4294967296) (-187008185/4294967296) 1 8 ![60,0,4] ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)] affine00309
theorem leaf00309_checked : FastNestedCellData.accepts 1 2 4 leaf00309=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (26207797507/1000000000000) (3936773525/4294967296) (-187008185/4294967296) 1 8 ![60,0,4] ![(9/1280),0,(1/2)] ![(1/6400),1,(1/2)] 19337941333889288443355704852480000000000 18189724392667494359304386733337439371264 694057727964705552366674378752000000000000 raw00309 affine00309
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00309_raw leaf00309_rectangular
    leaf00309_transform leaf00309_sign leaf00309_log
#print axioms leaf00309_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
