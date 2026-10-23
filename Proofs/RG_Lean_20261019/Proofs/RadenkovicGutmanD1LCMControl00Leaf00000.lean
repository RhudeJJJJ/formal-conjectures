/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerScaledCell
import Proofs.RadenkovicGutmanD1IntegerNorm00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMControls00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00000 : NestedInteger.Poly 3 := rg_integer_data% (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack false 337899918187240095744000000000000 13051747851183633338956186263 20737216539295399000000000000))
theorem leaf00000_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack false 337899918187240095744000000000000 13051747851183633338956186263 20737216539295399000000000000 raw00000=true := by decide +kernel
#print axioms leaf00000_raw
theorem leaf00000_rectangular : NestedInteger.rectangular 3 ![88,4,4] raw00000=true := by decide +kernel
#print axioms leaf00000_rectangular
def inner00000 : NestedInteger.Poly 3 := rg_integer_data% (IntegerAffineStages.inner raw00000 ![8,0,0] ![1,1,1] ![8000,256,256])
theorem leaf00000_inner : inner00000=(IntegerAffineStages.inner raw00000 ![8,0,0] ![1,1,1] ![8000,256,256]) := by decide +kernel
#print axioms leaf00000_inner
def affine00000 : NestedInteger.Poly 3 := rg_integer_data% (IntegerOuterTerms.transform 8 1 8000 0 inner00000)
theorem leaf00000_outer : affine00000=(IntegerOuterTerms.transform 8 1 8000 0 inner00000) := by decide +kernel
#print axioms leaf00000_outer
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine00000=true := by decide +kernel
#print axioms leaf00000_sign
theorem leaf00000_log : RationalLog.accepts (12727/536870912) (-22870244509/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00000_log
def leaf00000 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)] 337899918187240095744000000000000 ![8000,256,256] affine00000
theorem leaf00000_checked : FastNestedCellData.accepts 1 4 4 leaf00000=true :=
  IntegerScaledCell.accepts_make DegreeOneIntegerNorm00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)] 337899918187240095744000000000000 13051747851183633338956186263 20737216539295399000000000000 ![8,0,0] ![1,1,1] ![8000,256,256] raw00000 inner00000 affine00000
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf00000_raw leaf00000_rectangular leaf00000_inner leaf00000_outer leaf00000_sign leaf00000_log
#print axioms leaf00000_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLCMControls00
