/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerLiteral
import Proofs.RadenkovicGutmanD1Norm00Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneMaterializedLong00Control
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def certificate00000 : NestedInteger.Poly 3 := rg_integer_tensor%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack
    false (629387643537/1000000000000) (111948752516150571/4722366482869645213696) ![88,4,4]
    ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)])
def leaf00000 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack00.pack
    false (629387643537/1000000000000) (111948752516150571/4722366482869645213696) (-12573040328794530135869/2361183241434822606848)
    16 32 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]
theorem leaf00000_checked : FastNestedCellData.accepts 1 4 4 leaf00000=true := by
  apply IntegerLiteral.accepts_materialized (a := certificate00000)
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00000_checked
def certificate00001 : NestedInteger.Poly 3 := rg_integer_tensor%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack
    false (75273456011/200000000000) (116850080102088036055/590295810358705651712) ![88,4,4]
    ![(1/1000),0,(1/256)] ![(1/8000),(1/256),(1/256)])
def leaf00001 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack00.pack
    false (75273456011/200000000000) (116850080102088036055/590295810358705651712) (-3824484144323126304233/4722366482869645213696)
    3 32 ![88,4,4] ![(1/1000),0,(1/256)] ![(1/8000),(1/256),(1/256)]
theorem leaf00001_checked : FastNestedCellData.accepts 1 4 4 leaf00001=true := by
  apply IntegerLiteral.accepts_materialized (a := certificate00001)
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00001_checked
end Gebendorfer.RadenkovicGutman.DegreeOneMaterializedLong00Control
