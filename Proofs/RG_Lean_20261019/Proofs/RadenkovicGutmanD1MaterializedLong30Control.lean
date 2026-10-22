/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerLiteral
import Proofs.RadenkovicGutmanD1Norm30Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneMaterializedLong30Control
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def certificate00000 : NestedInteger.Poly 3 := rg_integer_tensor%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack
    false (48977026691/500000000000) (31081173261641959/4722366482869645213696) ![60,0,4]
    ![(1/1000),0,0] ![(1/16000),1,(1/16)])
def leaf00000 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack30.pack
    false (48977026691/500000000000) (31081173261641959/4722366482869645213696) (-14085896386395587873413/2361183241434822606848)
    18 32 ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)]
theorem leaf00000_checked : FastNestedCellData.accepts 1 2 4 leaf00000=true := by
  apply IntegerLiteral.accepts_materialized (a := certificate00000)
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00000_checked
def certificate00001 : NestedInteger.Poly 3 := rg_integer_tensor%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack
    false (16248457067/500000000000) (1058027733883975055239/1180591620717411303424) ![60,0,4]
    ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)])
def leaf00001 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack30.pack
    false (16248457067/500000000000) (1058027733883975055239/1180591620717411303424) (-258807263833253176393/4722366482869645213696)
    1 32 ![60,0,4] ![(1/1000),0,(1/16)] ![(1/16000),1,(1/16)]
theorem leaf00001_checked : FastNestedCellData.accepts 1 2 4 leaf00001=true := by
  apply IntegerLiteral.accepts_materialized (a := certificate00001)
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00001_checked
end Gebendorfer.RadenkovicGutman.DegreeOneMaterializedLong30Control
