/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPaidDegreeOneClass
import Proofs.RadenkovicGutmanD1Short33Cells00
import Proofs.RadenkovicGutmanD1Short33Cells01
import Proofs.RadenkovicGutmanD1Short33Cells02
import Proofs.RadenkovicGutmanD1Short33Cells03
import Proofs.RadenkovicGutmanD1Short33Cells04
import Proofs.RadenkovicGutmanD1Short33Cells05
import Proofs.RadenkovicGutmanD1Short33Cells06
import Proofs.RadenkovicGutmanD1Short33Cells07
import Proofs.RadenkovicGutmanD1Short33Cells08
import Proofs.RadenkovicGutmanD1Short33Cells09
import Proofs.RadenkovicGutmanD1Short33Cells10
import Proofs.RadenkovicGutmanD1Short33Cells11
import Proofs.RadenkovicGutmanD1Short33Cells12
import Proofs.RadenkovicGutmanD1Short33Cells13
import Proofs.RadenkovicGutmanD1Short33Cells14
import Proofs.RadenkovicGutmanD1Short33Cells15
import Proofs.RadenkovicGutmanD1Short33Cells16
import Proofs.RadenkovicGutmanD1Short33Cells17
import Proofs.RadenkovicGutmanD1Short33Cells18
import Proofs.RadenkovicGutmanD1Short33Cells19
import Proofs.RadenkovicGutmanD1Short33Cells20
import Proofs.RadenkovicGutmanD1Short33Cells21
import Proofs.RadenkovicGutmanD1Short33Cells22
import Proofs.RadenkovicGutmanD1Short33Cells23
import Proofs.RadenkovicGutmanD1Short33Cells24
import Proofs.RadenkovicGutmanD1Short33Cells25
import Proofs.RadenkovicGutmanD1Short33Cells26
import Proofs.RadenkovicGutmanD1Short33Cells27
import Proofs.RadenkovicGutmanD1Short33Cells28
import Proofs.RadenkovicGutmanD1Short33Cells29
import Proofs.RadenkovicGutmanD1Short33Cells30
import Proofs.RadenkovicGutmanD1Short33Cells31
import Proofs.RadenkovicGutmanD1Short33Cells32
import Proofs.RadenkovicGutmanD1Short33Cells33
import Proofs.RadenkovicGutmanD1Short33Cells34
import Proofs.RadenkovicGutmanD1Short33Cells35
import Proofs.RadenkovicGutmanD1Short33Cells36
import Proofs.RadenkovicGutmanD1Short33Cells37
namespace Gebendorfer.RadenkovicGutman.DegreeOneShortClass33
open CellPartition
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slice000 : Slice := ⟨cell000,(1/1000),(1/800)⟩
theorem slice000_checked : CellPartition.accepts 1 2 2 slice000=true :=
  accepts_of_checks 1 2 2 slice000 cell000_checked (by decide +kernel)
def slice001 : Slice := ⟨cell001,(1/800),(3/2000)⟩
theorem slice001_checked : CellPartition.accepts 1 2 2 slice001=true :=
  accepts_of_checks 1 2 2 slice001 cell001_checked (by decide +kernel)
def slice002 : Slice := ⟨cell002,(3/2000),(1/500)⟩
theorem slice002_checked : CellPartition.accepts 1 2 2 slice002=true :=
  accepts_of_checks 1 2 2 slice002 cell002_checked (by decide +kernel)
def slice003 : Slice := ⟨cell003,(1/500),(19/8000)⟩
theorem slice003_checked : CellPartition.accepts 1 2 2 slice003=true :=
  accepts_of_checks 1 2 2 slice003 cell003_checked (by decide +kernel)
def slice004 : Slice := ⟨cell004,(19/8000),(11/4000)⟩
theorem slice004_checked : CellPartition.accepts 1 2 2 slice004=true :=
  accepts_of_checks 1 2 2 slice004 cell004_checked (by decide +kernel)
def slice005 : Slice := ⟨cell005,(11/4000),(7/2000)⟩
theorem slice005_checked : CellPartition.accepts 1 2 2 slice005=true :=
  accepts_of_checks 1 2 2 slice005 cell005_checked (by decide +kernel)
def slice006 : Slice := ⟨cell006,(7/2000),(17/4000)⟩
theorem slice006_checked : CellPartition.accepts 1 2 2 slice006=true :=
  accepts_of_checks 1 2 2 slice006 cell006_checked (by decide +kernel)
def slice007 : Slice := ⟨cell007,(17/4000),(1/200)⟩
theorem slice007_checked : CellPartition.accepts 1 2 2 slice007=true :=
  accepts_of_checks 1 2 2 slice007 cell007_checked (by decide +kernel)
def slice008 : Slice := ⟨cell008,(1/200),(9/1600)⟩
theorem slice008_checked : CellPartition.accepts 1 2 2 slice008=true :=
  accepts_of_checks 1 2 2 slice008 cell008_checked (by decide +kernel)
def slice009 : Slice := ⟨cell009,(9/1600),(1/160)⟩
theorem slice009_checked : CellPartition.accepts 1 2 2 slice009=true :=
  accepts_of_checks 1 2 2 slice009 cell009_checked (by decide +kernel)
def slice010 : Slice := ⟨cell010,(1/160),(11/1600)⟩
theorem slice010_checked : CellPartition.accepts 1 2 2 slice010=true :=
  accepts_of_checks 1 2 2 slice010 cell010_checked (by decide +kernel)
def slice011 : Slice := ⟨cell011,(11/1600),(3/400)⟩
theorem slice011_checked : CellPartition.accepts 1 2 2 slice011=true :=
  accepts_of_checks 1 2 2 slice011 cell011_checked (by decide +kernel)
def slice012 : Slice := ⟨cell012,(3/400),(7/800)⟩
theorem slice012_checked : CellPartition.accepts 1 2 2 slice012=true :=
  accepts_of_checks 1 2 2 slice012 cell012_checked (by decide +kernel)
def slice013 : Slice := ⟨cell013,(7/800),(1/100)⟩
theorem slice013_checked : CellPartition.accepts 1 2 2 slice013=true :=
  accepts_of_checks 1 2 2 slice013 cell013_checked (by decide +kernel)
def slice014 : Slice := ⟨cell014,(1/100),(9/800)⟩
theorem slice014_checked : CellPartition.accepts 1 2 2 slice014=true :=
  accepts_of_checks 1 2 2 slice014 cell014_checked (by decide +kernel)
def slice015 : Slice := ⟨cell015,(9/800),(1/80)⟩
theorem slice015_checked : CellPartition.accepts 1 2 2 slice015=true :=
  accepts_of_checks 1 2 2 slice015 cell015_checked (by decide +kernel)
def slice016 : Slice := ⟨cell016,(1/80),(11/800)⟩
theorem slice016_checked : CellPartition.accepts 1 2 2 slice016=true :=
  accepts_of_checks 1 2 2 slice016 cell016_checked (by decide +kernel)
def slice017 : Slice := ⟨cell017,(11/800),(3/200)⟩
theorem slice017_checked : CellPartition.accepts 1 2 2 slice017=true :=
  accepts_of_checks 1 2 2 slice017 cell017_checked (by decide +kernel)
def slice018 : Slice := ⟨cell018,(3/200),(13/800)⟩
theorem slice018_checked : CellPartition.accepts 1 2 2 slice018=true :=
  accepts_of_checks 1 2 2 slice018 cell018_checked (by decide +kernel)
def slice019 : Slice := ⟨cell019,(13/800),(7/400)⟩
theorem slice019_checked : CellPartition.accepts 1 2 2 slice019=true :=
  accepts_of_checks 1 2 2 slice019 cell019_checked (by decide +kernel)
def slice020 : Slice := ⟨cell020,(7/400),(3/160)⟩
theorem slice020_checked : CellPartition.accepts 1 2 2 slice020=true :=
  accepts_of_checks 1 2 2 slice020 cell020_checked (by decide +kernel)
def slice021 : Slice := ⟨cell021,(3/160),(1/50)⟩
theorem slice021_checked : CellPartition.accepts 1 2 2 slice021=true :=
  accepts_of_checks 1 2 2 slice021 cell021_checked (by decide +kernel)
def slice022 : Slice := ⟨cell022,(1/50),(7/320)⟩
theorem slice022_checked : CellPartition.accepts 1 2 2 slice022=true :=
  accepts_of_checks 1 2 2 slice022 cell022_checked (by decide +kernel)
def slice023 : Slice := ⟨cell023,(7/320),(19/800)⟩
theorem slice023_checked : CellPartition.accepts 1 2 2 slice023=true :=
  accepts_of_checks 1 2 2 slice023 cell023_checked (by decide +kernel)
def slice024 : Slice := ⟨cell024,(19/800),(41/1600)⟩
theorem slice024_checked : CellPartition.accepts 1 2 2 slice024=true :=
  accepts_of_checks 1 2 2 slice024 cell024_checked (by decide +kernel)
def slice025 : Slice := ⟨cell025,(41/1600),(11/400)⟩
theorem slice025_checked : CellPartition.accepts 1 2 2 slice025=true :=
  accepts_of_checks 1 2 2 slice025 cell025_checked (by decide +kernel)
def slice026 : Slice := ⟨cell026,(11/400),(47/1600)⟩
theorem slice026_checked : CellPartition.accepts 1 2 2 slice026=true :=
  accepts_of_checks 1 2 2 slice026 cell026_checked (by decide +kernel)
def slice027 : Slice := ⟨cell027,(47/1600),(1/32)⟩
theorem slice027_checked : CellPartition.accepts 1 2 2 slice027=true :=
  accepts_of_checks 1 2 2 slice027 cell027_checked (by decide +kernel)
def slice028 : Slice := ⟨cell028,(1/32),(53/1600)⟩
theorem slice028_checked : CellPartition.accepts 1 2 2 slice028=true :=
  accepts_of_checks 1 2 2 slice028 cell028_checked (by decide +kernel)
def slice029 : Slice := ⟨cell029,(53/1600),(7/200)⟩
theorem slice029_checked : CellPartition.accepts 1 2 2 slice029=true :=
  accepts_of_checks 1 2 2 slice029 cell029_checked (by decide +kernel)
def slice030 : Slice := ⟨cell030,(7/200),(59/1600)⟩
theorem slice030_checked : CellPartition.accepts 1 2 2 slice030=true :=
  accepts_of_checks 1 2 2 slice030 cell030_checked (by decide +kernel)
def slice031 : Slice := ⟨cell031,(59/1600),(31/800)⟩
theorem slice031_checked : CellPartition.accepts 1 2 2 slice031=true :=
  accepts_of_checks 1 2 2 slice031 cell031_checked (by decide +kernel)
def slice032 : Slice := ⟨cell032,(31/800),(13/320)⟩
theorem slice032_checked : CellPartition.accepts 1 2 2 slice032=true :=
  accepts_of_checks 1 2 2 slice032 cell032_checked (by decide +kernel)
def slice033 : Slice := ⟨cell033,(13/320),(17/400)⟩
theorem slice033_checked : CellPartition.accepts 1 2 2 slice033=true :=
  accepts_of_checks 1 2 2 slice033 cell033_checked (by decide +kernel)
def slice034 : Slice := ⟨cell034,(17/400),(71/1600)⟩
theorem slice034_checked : CellPartition.accepts 1 2 2 slice034=true :=
  accepts_of_checks 1 2 2 slice034 cell034_checked (by decide +kernel)
def slice035 : Slice := ⟨cell035,(71/1600),(37/800)⟩
theorem slice035_checked : CellPartition.accepts 1 2 2 slice035=true :=
  accepts_of_checks 1 2 2 slice035 cell035_checked (by decide +kernel)
def slice036 : Slice := ⟨cell036,(37/800),(77/1600)⟩
theorem slice036_checked : CellPartition.accepts 1 2 2 slice036=true :=
  accepts_of_checks 1 2 2 slice036 cell036_checked (by decide +kernel)
def slice037 : Slice := ⟨cell037,(77/1600),(1/20)⟩
theorem slice037_checked : CellPartition.accepts 1 2 2 slice037=true :=
  accepts_of_checks 1 2 2 slice037 cell037_checked (by decide +kernel)
def slice038 : Slice := ⟨cell038,(1/20),(17/320)⟩
theorem slice038_checked : CellPartition.accepts 1 2 2 slice038=true :=
  accepts_of_checks 1 2 2 slice038 cell038_checked (by decide +kernel)
def slice039 : Slice := ⟨cell039,(17/320),(9/160)⟩
theorem slice039_checked : CellPartition.accepts 1 2 2 slice039=true :=
  accepts_of_checks 1 2 2 slice039 cell039_checked (by decide +kernel)
def slice040 : Slice := ⟨cell040,(9/160),(19/320)⟩
theorem slice040_checked : CellPartition.accepts 1 2 2 slice040=true :=
  accepts_of_checks 1 2 2 slice040 cell040_checked (by decide +kernel)
def slice041 : Slice := ⟨cell041,(19/320),(1/16)⟩
theorem slice041_checked : CellPartition.accepts 1 2 2 slice041=true :=
  accepts_of_checks 1 2 2 slice041 cell041_checked (by decide +kernel)
def slice042 : Slice := ⟨cell042,(1/16),(21/320)⟩
theorem slice042_checked : CellPartition.accepts 1 2 2 slice042=true :=
  accepts_of_checks 1 2 2 slice042 cell042_checked (by decide +kernel)
def slice043 : Slice := ⟨cell043,(21/320),(11/160)⟩
theorem slice043_checked : CellPartition.accepts 1 2 2 slice043=true :=
  accepts_of_checks 1 2 2 slice043 cell043_checked (by decide +kernel)
def slice044 : Slice := ⟨cell044,(11/160),(23/320)⟩
theorem slice044_checked : CellPartition.accepts 1 2 2 slice044=true :=
  accepts_of_checks 1 2 2 slice044 cell044_checked (by decide +kernel)
def slice045 : Slice := ⟨cell045,(23/320),(3/40)⟩
theorem slice045_checked : CellPartition.accepts 1 2 2 slice045=true :=
  accepts_of_checks 1 2 2 slice045 cell045_checked (by decide +kernel)
def slice046 : Slice := ⟨cell046,(3/40),(5/64)⟩
theorem slice046_checked : CellPartition.accepts 1 2 2 slice046=true :=
  accepts_of_checks 1 2 2 slice046 cell046_checked (by decide +kernel)
def slice047 : Slice := ⟨cell047,(5/64),(13/160)⟩
theorem slice047_checked : CellPartition.accepts 1 2 2 slice047=true :=
  accepts_of_checks 1 2 2 slice047 cell047_checked (by decide +kernel)
def slice048 : Slice := ⟨cell048,(13/160),(27/320)⟩
theorem slice048_checked : CellPartition.accepts 1 2 2 slice048=true :=
  accepts_of_checks 1 2 2 slice048 cell048_checked (by decide +kernel)
def slice049 : Slice := ⟨cell049,(27/320),(7/80)⟩
theorem slice049_checked : CellPartition.accepts 1 2 2 slice049=true :=
  accepts_of_checks 1 2 2 slice049 cell049_checked (by decide +kernel)
def slice050 : Slice := ⟨cell050,(7/80),(29/320)⟩
theorem slice050_checked : CellPartition.accepts 1 2 2 slice050=true :=
  accepts_of_checks 1 2 2 slice050 cell050_checked (by decide +kernel)
def slice051 : Slice := ⟨cell051,(29/320),(3/32)⟩
theorem slice051_checked : CellPartition.accepts 1 2 2 slice051=true :=
  accepts_of_checks 1 2 2 slice051 cell051_checked (by decide +kernel)
def slice052 : Slice := ⟨cell052,(3/32),(31/320)⟩
theorem slice052_checked : CellPartition.accepts 1 2 2 slice052=true :=
  accepts_of_checks 1 2 2 slice052 cell052_checked (by decide +kernel)
def slice053 : Slice := ⟨cell053,(31/320),(1/10)⟩
theorem slice053_checked : CellPartition.accepts 1 2 2 slice053=true :=
  accepts_of_checks 1 2 2 slice053 cell053_checked (by decide +kernel)
def slice054 : Slice := ⟨cell054,(1/10),(33/320)⟩
theorem slice054_checked : CellPartition.accepts 1 2 2 slice054=true :=
  accepts_of_checks 1 2 2 slice054 cell054_checked (by decide +kernel)
def slice055 : Slice := ⟨cell055,(33/320),(17/160)⟩
theorem slice055_checked : CellPartition.accepts 1 2 2 slice055=true :=
  accepts_of_checks 1 2 2 slice055 cell055_checked (by decide +kernel)
def slice056 : Slice := ⟨cell056,(17/160),(7/64)⟩
theorem slice056_checked : CellPartition.accepts 1 2 2 slice056=true :=
  accepts_of_checks 1 2 2 slice056 cell056_checked (by decide +kernel)
def slice057 : Slice := ⟨cell057,(7/64),(9/80)⟩
theorem slice057_checked : CellPartition.accepts 1 2 2 slice057=true :=
  accepts_of_checks 1 2 2 slice057 cell057_checked (by decide +kernel)
def slice058 : Slice := ⟨cell058,(9/80),(37/320)⟩
theorem slice058_checked : CellPartition.accepts 1 2 2 slice058=true :=
  accepts_of_checks 1 2 2 slice058 cell058_checked (by decide +kernel)
def slice059 : Slice := ⟨cell059,(37/320),(19/160)⟩
theorem slice059_checked : CellPartition.accepts 1 2 2 slice059=true :=
  accepts_of_checks 1 2 2 slice059 cell059_checked (by decide +kernel)
def slice060 : Slice := ⟨cell060,(19/160),(39/320)⟩
theorem slice060_checked : CellPartition.accepts 1 2 2 slice060=true :=
  accepts_of_checks 1 2 2 slice060 cell060_checked (by decide +kernel)
def slice061 : Slice := ⟨cell061,(39/320),(1/8)⟩
theorem slice061_checked : CellPartition.accepts 1 2 2 slice061=true :=
  accepts_of_checks 1 2 2 slice061 cell061_checked (by decide +kernel)
def slice062 : Slice := ⟨cell062,(1/8),(41/320)⟩
theorem slice062_checked : CellPartition.accepts 1 2 2 slice062=true :=
  accepts_of_checks 1 2 2 slice062 cell062_checked (by decide +kernel)
def slice063 : Slice := ⟨cell063,(41/320),(21/160)⟩
theorem slice063_checked : CellPartition.accepts 1 2 2 slice063=true :=
  accepts_of_checks 1 2 2 slice063 cell063_checked (by decide +kernel)
def slice064 : Slice := ⟨cell064,(21/160),(43/320)⟩
theorem slice064_checked : CellPartition.accepts 1 2 2 slice064=true :=
  accepts_of_checks 1 2 2 slice064 cell064_checked (by decide +kernel)
def slice065 : Slice := ⟨cell065,(43/320),(11/80)⟩
theorem slice065_checked : CellPartition.accepts 1 2 2 slice065=true :=
  accepts_of_checks 1 2 2 slice065 cell065_checked (by decide +kernel)
def slice066 : Slice := ⟨cell066,(11/80),(9/64)⟩
theorem slice066_checked : CellPartition.accepts 1 2 2 slice066=true :=
  accepts_of_checks 1 2 2 slice066 cell066_checked (by decide +kernel)
def slice067 : Slice := ⟨cell067,(9/64),(23/160)⟩
theorem slice067_checked : CellPartition.accepts 1 2 2 slice067=true :=
  accepts_of_checks 1 2 2 slice067 cell067_checked (by decide +kernel)
def slice068 : Slice := ⟨cell068,(23/160),(3/20)⟩
theorem slice068_checked : CellPartition.accepts 1 2 2 slice068=true :=
  accepts_of_checks 1 2 2 slice068 cell068_checked (by decide +kernel)
def slice069 : Slice := ⟨cell069,(3/20),(5/32)⟩
theorem slice069_checked : CellPartition.accepts 1 2 2 slice069=true :=
  accepts_of_checks 1 2 2 slice069 cell069_checked (by decide +kernel)
def slice070 : Slice := ⟨cell070,(5/32),(13/80)⟩
theorem slice070_checked : CellPartition.accepts 1 2 2 slice070=true :=
  accepts_of_checks 1 2 2 slice070 cell070_checked (by decide +kernel)
def slice071 : Slice := ⟨cell071,(13/80),(27/160)⟩
theorem slice071_checked : CellPartition.accepts 1 2 2 slice071=true :=
  accepts_of_checks 1 2 2 slice071 cell071_checked (by decide +kernel)
def slice072 : Slice := ⟨cell072,(27/160),(7/40)⟩
theorem slice072_checked : CellPartition.accepts 1 2 2 slice072=true :=
  accepts_of_checks 1 2 2 slice072 cell072_checked (by decide +kernel)
def slice073 : Slice := ⟨cell073,(7/40),(29/160)⟩
theorem slice073_checked : CellPartition.accepts 1 2 2 slice073=true :=
  accepts_of_checks 1 2 2 slice073 cell073_checked (by decide +kernel)
def slice074 : Slice := ⟨cell074,(29/160),(3/16)⟩
theorem slice074_checked : CellPartition.accepts 1 2 2 slice074=true :=
  accepts_of_checks 1 2 2 slice074 cell074_checked (by decide +kernel)
def slice075 : Slice := ⟨cell075,(3/16),(31/160)⟩
theorem slice075_checked : CellPartition.accepts 1 2 2 slice075=true :=
  accepts_of_checks 1 2 2 slice075 cell075_checked (by decide +kernel)
def slice076 : Slice := ⟨cell076,(31/160),(1/5)⟩
theorem slice076_checked : CellPartition.accepts 1 2 2 slice076=true :=
  accepts_of_checks 1 2 2 slice076 cell076_checked (by decide +kernel)
def slice077 : Slice := ⟨cell077,(1/5),(131/640)⟩
theorem slice077_checked : CellPartition.accepts 1 2 2 slice077=true :=
  accepts_of_checks 1 2 2 slice077 cell077_checked (by decide +kernel)
def slice078 : Slice := ⟨cell078,(131/640),(67/320)⟩
theorem slice078_checked : CellPartition.accepts 1 2 2 slice078=true :=
  accepts_of_checks 1 2 2 slice078 cell078_checked (by decide +kernel)
def slice079 : Slice := ⟨cell079,(67/320),(137/640)⟩
theorem slice079_checked : CellPartition.accepts 1 2 2 slice079=true :=
  accepts_of_checks 1 2 2 slice079 cell079_checked (by decide +kernel)
def slice080 : Slice := ⟨cell080,(137/640),(7/32)⟩
theorem slice080_checked : CellPartition.accepts 1 2 2 slice080=true :=
  accepts_of_checks 1 2 2 slice080 cell080_checked (by decide +kernel)
def slice081 : Slice := ⟨cell081,(7/32),(143/640)⟩
theorem slice081_checked : CellPartition.accepts 1 2 2 slice081=true :=
  accepts_of_checks 1 2 2 slice081 cell081_checked (by decide +kernel)
def slice082 : Slice := ⟨cell082,(143/640),(73/320)⟩
theorem slice082_checked : CellPartition.accepts 1 2 2 slice082=true :=
  accepts_of_checks 1 2 2 slice082 cell082_checked (by decide +kernel)
def slice083 : Slice := ⟨cell083,(73/320),(149/640)⟩
theorem slice083_checked : CellPartition.accepts 1 2 2 slice083=true :=
  accepts_of_checks 1 2 2 slice083 cell083_checked (by decide +kernel)
def slice084 : Slice := ⟨cell084,(149/640),(19/80)⟩
theorem slice084_checked : CellPartition.accepts 1 2 2 slice084=true :=
  accepts_of_checks 1 2 2 slice084 cell084_checked (by decide +kernel)
def slice085 : Slice := ⟨cell085,(19/80),(79/320)⟩
theorem slice085_checked : CellPartition.accepts 1 2 2 slice085=true :=
  accepts_of_checks 1 2 2 slice085 cell085_checked (by decide +kernel)
def slice086 : Slice := ⟨cell086,(79/320),(41/160)⟩
theorem slice086_checked : CellPartition.accepts 1 2 2 slice086=true :=
  accepts_of_checks 1 2 2 slice086 cell086_checked (by decide +kernel)
def slice087 : Slice := ⟨cell087,(41/160),(17/64)⟩
theorem slice087_checked : CellPartition.accepts 1 2 2 slice087=true :=
  accepts_of_checks 1 2 2 slice087 cell087_checked (by decide +kernel)
def slice088 : Slice := ⟨cell088,(17/64),(11/40)⟩
theorem slice088_checked : CellPartition.accepts 1 2 2 slice088=true :=
  accepts_of_checks 1 2 2 slice088 cell088_checked (by decide +kernel)
def slice089 : Slice := ⟨cell089,(11/40),(91/320)⟩
theorem slice089_checked : CellPartition.accepts 1 2 2 slice089=true :=
  accepts_of_checks 1 2 2 slice089 cell089_checked (by decide +kernel)
def slice090 : Slice := ⟨cell090,(91/320),(47/160)⟩
theorem slice090_checked : CellPartition.accepts 1 2 2 slice090=true :=
  accepts_of_checks 1 2 2 slice090 cell090_checked (by decide +kernel)
def slice091 : Slice := ⟨cell091,(47/160),(97/320)⟩
theorem slice091_checked : CellPartition.accepts 1 2 2 slice091=true :=
  accepts_of_checks 1 2 2 slice091 cell091_checked (by decide +kernel)
def slice092 : Slice := ⟨cell092,(97/320),(5/16)⟩
theorem slice092_checked : CellPartition.accepts 1 2 2 slice092=true :=
  accepts_of_checks 1 2 2 slice092 cell092_checked (by decide +kernel)
def slice093 : Slice := ⟨cell093,(5/16),(103/320)⟩
theorem slice093_checked : CellPartition.accepts 1 2 2 slice093=true :=
  accepts_of_checks 1 2 2 slice093 cell093_checked (by decide +kernel)
def slice094 : Slice := ⟨cell094,(103/320),(53/160)⟩
theorem slice094_checked : CellPartition.accepts 1 2 2 slice094=true :=
  accepts_of_checks 1 2 2 slice094 cell094_checked (by decide +kernel)
def slice095 : Slice := ⟨cell095,(53/160),(109/320)⟩
theorem slice095_checked : CellPartition.accepts 1 2 2 slice095=true :=
  accepts_of_checks 1 2 2 slice095 cell095_checked (by decide +kernel)
def slice096 : Slice := ⟨cell096,(109/320),(7/20)⟩
theorem slice096_checked : CellPartition.accepts 1 2 2 slice096=true :=
  accepts_of_checks 1 2 2 slice096 cell096_checked (by decide +kernel)
def slice097 : Slice := ⟨cell097,(7/20),(23/64)⟩
theorem slice097_checked : CellPartition.accepts 1 2 2 slice097=true :=
  accepts_of_checks 1 2 2 slice097 cell097_checked (by decide +kernel)
def slice098 : Slice := ⟨cell098,(23/64),(59/160)⟩
theorem slice098_checked : CellPartition.accepts 1 2 2 slice098=true :=
  accepts_of_checks 1 2 2 slice098 cell098_checked (by decide +kernel)
def slice099 : Slice := ⟨cell099,(59/160),(121/320)⟩
theorem slice099_checked : CellPartition.accepts 1 2 2 slice099=true :=
  accepts_of_checks 1 2 2 slice099 cell099_checked (by decide +kernel)
def slice100 : Slice := ⟨cell100,(121/320),(31/80)⟩
theorem slice100_checked : CellPartition.accepts 1 2 2 slice100=true :=
  accepts_of_checks 1 2 2 slice100 cell100_checked (by decide +kernel)
def slice101 : Slice := ⟨cell101,(31/80),(127/320)⟩
theorem slice101_checked : CellPartition.accepts 1 2 2 slice101=true :=
  accepts_of_checks 1 2 2 slice101 cell101_checked (by decide +kernel)
def slice102 : Slice := ⟨cell102,(127/320),(13/32)⟩
theorem slice102_checked : CellPartition.accepts 1 2 2 slice102=true :=
  accepts_of_checks 1 2 2 slice102 cell102_checked (by decide +kernel)
def slice103 : Slice := ⟨cell103,(13/32),(133/320)⟩
theorem slice103_checked : CellPartition.accepts 1 2 2 slice103=true :=
  accepts_of_checks 1 2 2 slice103 cell103_checked (by decide +kernel)
def slice104 : Slice := ⟨cell104,(133/320),(17/40)⟩
theorem slice104_checked : CellPartition.accepts 1 2 2 slice104=true :=
  accepts_of_checks 1 2 2 slice104 cell104_checked (by decide +kernel)
def slice105 : Slice := ⟨cell105,(17/40),(139/320)⟩
theorem slice105_checked : CellPartition.accepts 1 2 2 slice105=true :=
  accepts_of_checks 1 2 2 slice105 cell105_checked (by decide +kernel)
def slice106 : Slice := ⟨cell106,(139/320),(71/160)⟩
theorem slice106_checked : CellPartition.accepts 1 2 2 slice106=true :=
  accepts_of_checks 1 2 2 slice106 cell106_checked (by decide +kernel)
def slice107 : Slice := ⟨cell107,(71/160),(29/64)⟩
theorem slice107_checked : CellPartition.accepts 1 2 2 slice107=true :=
  accepts_of_checks 1 2 2 slice107 cell107_checked (by decide +kernel)
def slice108 : Slice := ⟨cell108,(29/64),(37/80)⟩
theorem slice108_checked : CellPartition.accepts 1 2 2 slice108=true :=
  accepts_of_checks 1 2 2 slice108 cell108_checked (by decide +kernel)
def slice109 : Slice := ⟨cell109,(37/80),(151/320)⟩
theorem slice109_checked : CellPartition.accepts 1 2 2 slice109=true :=
  accepts_of_checks 1 2 2 slice109 cell109_checked (by decide +kernel)
def slice110 : Slice := ⟨cell110,(151/320),(77/160)⟩
theorem slice110_checked : CellPartition.accepts 1 2 2 slice110=true :=
  accepts_of_checks 1 2 2 slice110 cell110_checked (by decide +kernel)
def slice111 : Slice := ⟨cell111,(77/160),(1/2)⟩
theorem slice111_checked : CellPartition.accepts 1 2 2 slice111=true :=
  accepts_of_checks 1 2 2 slice111 cell111_checked (by decide +kernel)
def slice112 : Slice := ⟨cell112,(1/2),(33/64)⟩
theorem slice112_checked : CellPartition.accepts 1 2 2 slice112=true :=
  accepts_of_checks 1 2 2 slice112 cell112_checked (by decide +kernel)
def slice113 : Slice := ⟨cell113,(33/64),(17/32)⟩
theorem slice113_checked : CellPartition.accepts 1 2 2 slice113=true :=
  accepts_of_checks 1 2 2 slice113 cell113_checked (by decide +kernel)
def slice114 : Slice := ⟨cell114,(17/32),(35/64)⟩
theorem slice114_checked : CellPartition.accepts 1 2 2 slice114=true :=
  accepts_of_checks 1 2 2 slice114 cell114_checked (by decide +kernel)
def slice115 : Slice := ⟨cell115,(35/64),(9/16)⟩
theorem slice115_checked : CellPartition.accepts 1 2 2 slice115=true :=
  accepts_of_checks 1 2 2 slice115 cell115_checked (by decide +kernel)
def slice116 : Slice := ⟨cell116,(9/16),(37/64)⟩
theorem slice116_checked : CellPartition.accepts 1 2 2 slice116=true :=
  accepts_of_checks 1 2 2 slice116 cell116_checked (by decide +kernel)
def slice117 : Slice := ⟨cell117,(37/64),(19/32)⟩
theorem slice117_checked : CellPartition.accepts 1 2 2 slice117=true :=
  accepts_of_checks 1 2 2 slice117 cell117_checked (by decide +kernel)
def slice118 : Slice := ⟨cell118,(19/32),(39/64)⟩
theorem slice118_checked : CellPartition.accepts 1 2 2 slice118=true :=
  accepts_of_checks 1 2 2 slice118 cell118_checked (by decide +kernel)
def slice119 : Slice := ⟨cell119,(39/64),(5/8)⟩
theorem slice119_checked : CellPartition.accepts 1 2 2 slice119=true :=
  accepts_of_checks 1 2 2 slice119 cell119_checked (by decide +kernel)
def slice120 : Slice := ⟨cell120,(5/8),(41/64)⟩
theorem slice120_checked : CellPartition.accepts 1 2 2 slice120=true :=
  accepts_of_checks 1 2 2 slice120 cell120_checked (by decide +kernel)
def slice121 : Slice := ⟨cell121,(41/64),(21/32)⟩
theorem slice121_checked : CellPartition.accepts 1 2 2 slice121=true :=
  accepts_of_checks 1 2 2 slice121 cell121_checked (by decide +kernel)
def slice122 : Slice := ⟨cell122,(21/32),(43/64)⟩
theorem slice122_checked : CellPartition.accepts 1 2 2 slice122=true :=
  accepts_of_checks 1 2 2 slice122 cell122_checked (by decide +kernel)
def slice123 : Slice := ⟨cell123,(43/64),(11/16)⟩
theorem slice123_checked : CellPartition.accepts 1 2 2 slice123=true :=
  accepts_of_checks 1 2 2 slice123 cell123_checked (by decide +kernel)
def slice124 : Slice := ⟨cell124,(11/16),(45/64)⟩
theorem slice124_checked : CellPartition.accepts 1 2 2 slice124=true :=
  accepts_of_checks 1 2 2 slice124 cell124_checked (by decide +kernel)
def slice125 : Slice := ⟨cell125,(45/64),(23/32)⟩
theorem slice125_checked : CellPartition.accepts 1 2 2 slice125=true :=
  accepts_of_checks 1 2 2 slice125 cell125_checked (by decide +kernel)
def slice126 : Slice := ⟨cell126,(23/32),(3/4)⟩
theorem slice126_checked : CellPartition.accepts 1 2 2 slice126=true :=
  accepts_of_checks 1 2 2 slice126 cell126_checked (by decide +kernel)
def slice127 : Slice := ⟨cell127,(3/4),(25/32)⟩
theorem slice127_checked : CellPartition.accepts 1 2 2 slice127=true :=
  accepts_of_checks 1 2 2 slice127 cell127_checked (by decide +kernel)
def slice128 : Slice := ⟨cell128,(25/32),(13/16)⟩
theorem slice128_checked : CellPartition.accepts 1 2 2 slice128=true :=
  accepts_of_checks 1 2 2 slice128 cell128_checked (by decide +kernel)
def slice129 : Slice := ⟨cell129,(13/16),(27/32)⟩
theorem slice129_checked : CellPartition.accepts 1 2 2 slice129=true :=
  accepts_of_checks 1 2 2 slice129 cell129_checked (by decide +kernel)
def slice130 : Slice := ⟨cell130,(27/32),(7/8)⟩
theorem slice130_checked : CellPartition.accepts 1 2 2 slice130=true :=
  accepts_of_checks 1 2 2 slice130 cell130_checked (by decide +kernel)
def slice131 : Slice := ⟨cell131,(7/8),(29/32)⟩
theorem slice131_checked : CellPartition.accepts 1 2 2 slice131=true :=
  accepts_of_checks 1 2 2 slice131 cell131_checked (by decide +kernel)
def slice132 : Slice := ⟨cell132,(29/32),(15/16)⟩
theorem slice132_checked : CellPartition.accepts 1 2 2 slice132=true :=
  accepts_of_checks 1 2 2 slice132 cell132_checked (by decide +kernel)
def slice133 : Slice := ⟨cell133,(15/16),(31/32)⟩
theorem slice133_checked : CellPartition.accepts 1 2 2 slice133=true :=
  accepts_of_checks 1 2 2 slice133 cell133_checked (by decide +kernel)
def slice134 : Slice := ⟨cell134,(31/32),1⟩
theorem slice134_checked : CellPartition.accepts 1 2 2 slice134=true :=
  accepts_of_checks 1 2 2 slice134 cell134_checked (by decide +kernel)
def slice135 : Slice := ⟨cell135,1,(32/31)⟩
theorem slice135_checked : CellPartition.accepts 1 2 2 slice135=true :=
  accepts_of_checks 1 2 2 slice135 cell135_checked (by decide +kernel)
def slice136 : Slice := ⟨cell136,(32/31),(16/15)⟩
theorem slice136_checked : CellPartition.accepts 1 2 2 slice136=true :=
  accepts_of_checks 1 2 2 slice136 cell136_checked (by decide +kernel)
def slice137 : Slice := ⟨cell137,(16/15),(32/29)⟩
theorem slice137_checked : CellPartition.accepts 1 2 2 slice137=true :=
  accepts_of_checks 1 2 2 slice137 cell137_checked (by decide +kernel)
def slice138 : Slice := ⟨cell138,(32/29),(8/7)⟩
theorem slice138_checked : CellPartition.accepts 1 2 2 slice138=true :=
  accepts_of_checks 1 2 2 slice138 cell138_checked (by decide +kernel)
def slice139 : Slice := ⟨cell139,(8/7),(32/27)⟩
theorem slice139_checked : CellPartition.accepts 1 2 2 slice139=true :=
  accepts_of_checks 1 2 2 slice139 cell139_checked (by decide +kernel)
def slice140 : Slice := ⟨cell140,(32/27),(16/13)⟩
theorem slice140_checked : CellPartition.accepts 1 2 2 slice140=true :=
  accepts_of_checks 1 2 2 slice140 cell140_checked (by decide +kernel)
def slice141 : Slice := ⟨cell141,(16/13),(32/25)⟩
theorem slice141_checked : CellPartition.accepts 1 2 2 slice141=true :=
  accepts_of_checks 1 2 2 slice141 cell141_checked (by decide +kernel)
def slice142 : Slice := ⟨cell142,(32/25),(4/3)⟩
theorem slice142_checked : CellPartition.accepts 1 2 2 slice142=true :=
  accepts_of_checks 1 2 2 slice142 cell142_checked (by decide +kernel)
def slice143 : Slice := ⟨cell143,(4/3),(16/11)⟩
theorem slice143_checked : CellPartition.accepts 1 2 2 slice143=true :=
  accepts_of_checks 1 2 2 slice143 cell143_checked (by decide +kernel)
def slice144 : Slice := ⟨cell144,(16/11),(32/21)⟩
theorem slice144_checked : CellPartition.accepts 1 2 2 slice144=true :=
  accepts_of_checks 1 2 2 slice144 cell144_checked (by decide +kernel)
def slice145 : Slice := ⟨cell145,(32/21),(8/5)⟩
theorem slice145_checked : CellPartition.accepts 1 2 2 slice145=true :=
  accepts_of_checks 1 2 2 slice145 cell145_checked (by decide +kernel)
def slice146 : Slice := ⟨cell146,(8/5),(32/19)⟩
theorem slice146_checked : CellPartition.accepts 1 2 2 slice146=true :=
  accepts_of_checks 1 2 2 slice146 cell146_checked (by decide +kernel)
def slice147 : Slice := ⟨cell147,(32/19),(16/9)⟩
theorem slice147_checked : CellPartition.accepts 1 2 2 slice147=true :=
  accepts_of_checks 1 2 2 slice147 cell147_checked (by decide +kernel)
def slice148 : Slice := ⟨cell148,(16/9),(64/35)⟩
theorem slice148_checked : CellPartition.accepts 1 2 2 slice148=true :=
  accepts_of_checks 1 2 2 slice148 cell148_checked (by decide +kernel)
def slice149 : Slice := ⟨cell149,(64/35),(32/17)⟩
theorem slice149_checked : CellPartition.accepts 1 2 2 slice149=true :=
  accepts_of_checks 1 2 2 slice149 cell149_checked (by decide +kernel)
def slice150 : Slice := ⟨cell150,(32/17),(64/33)⟩
theorem slice150_checked : CellPartition.accepts 1 2 2 slice150=true :=
  accepts_of_checks 1 2 2 slice150 cell150_checked (by decide +kernel)
def slice151 : Slice := ⟨cell151,(64/33),2⟩
theorem slice151_checked : CellPartition.accepts 1 2 2 slice151=true :=
  accepts_of_checks 1 2 2 slice151 cell151_checked (by decide +kernel)
def slice152 : Slice := ⟨cell152,2,(64/31)⟩
theorem slice152_checked : CellPartition.accepts 1 2 2 slice152=true :=
  accepts_of_checks 1 2 2 slice152 cell152_checked (by decide +kernel)
def slice153 : Slice := ⟨cell153,(64/31),(32/15)⟩
theorem slice153_checked : CellPartition.accepts 1 2 2 slice153=true :=
  accepts_of_checks 1 2 2 slice153 cell153_checked (by decide +kernel)
def slice154 : Slice := ⟨cell154,(32/15),(64/29)⟩
theorem slice154_checked : CellPartition.accepts 1 2 2 slice154=true :=
  accepts_of_checks 1 2 2 slice154 cell154_checked (by decide +kernel)
def slice155 : Slice := ⟨cell155,(64/29),(16/7)⟩
theorem slice155_checked : CellPartition.accepts 1 2 2 slice155=true :=
  accepts_of_checks 1 2 2 slice155 cell155_checked (by decide +kernel)
def slice156 : Slice := ⟨cell156,(16/7),(64/27)⟩
theorem slice156_checked : CellPartition.accepts 1 2 2 slice156=true :=
  accepts_of_checks 1 2 2 slice156 cell156_checked (by decide +kernel)
def slice157 : Slice := ⟨cell157,(64/27),(128/53)⟩
theorem slice157_checked : CellPartition.accepts 1 2 2 slice157=true :=
  accepts_of_checks 1 2 2 slice157 cell157_checked (by decide +kernel)
def slice158 : Slice := ⟨cell158,(128/53),(32/13)⟩
theorem slice158_checked : CellPartition.accepts 1 2 2 slice158=true :=
  accepts_of_checks 1 2 2 slice158 cell158_checked (by decide +kernel)
def slice159 : Slice := ⟨cell159,(32/13),(128/51)⟩
theorem slice159_checked : CellPartition.accepts 1 2 2 slice159=true :=
  accepts_of_checks 1 2 2 slice159 cell159_checked (by decide +kernel)
def slice160 : Slice := ⟨cell160,(128/51),(64/25)⟩
theorem slice160_checked : CellPartition.accepts 1 2 2 slice160=true :=
  accepts_of_checks 1 2 2 slice160 cell160_checked (by decide +kernel)
def slice161 : Slice := ⟨cell161,(64/25),(128/49)⟩
theorem slice161_checked : CellPartition.accepts 1 2 2 slice161=true :=
  accepts_of_checks 1 2 2 slice161 cell161_checked (by decide +kernel)
def slice162 : Slice := ⟨cell162,(128/49),(8/3)⟩
theorem slice162_checked : CellPartition.accepts 1 2 2 slice162=true :=
  accepts_of_checks 1 2 2 slice162 cell162_checked (by decide +kernel)
def slice163 : Slice := ⟨cell163,(8/3),(128/47)⟩
theorem slice163_checked : CellPartition.accepts 1 2 2 slice163=true :=
  accepts_of_checks 1 2 2 slice163 cell163_checked (by decide +kernel)
def slice164 : Slice := ⟨cell164,(128/47),(64/23)⟩
theorem slice164_checked : CellPartition.accepts 1 2 2 slice164=true :=
  accepts_of_checks 1 2 2 slice164 cell164_checked (by decide +kernel)
def slice165 : Slice := ⟨cell165,(64/23),(128/45)⟩
theorem slice165_checked : CellPartition.accepts 1 2 2 slice165=true :=
  accepts_of_checks 1 2 2 slice165 cell165_checked (by decide +kernel)
def slice166 : Slice := ⟨cell166,(128/45),(32/11)⟩
theorem slice166_checked : CellPartition.accepts 1 2 2 slice166=true :=
  accepts_of_checks 1 2 2 slice166 cell166_checked (by decide +kernel)
def slice167 : Slice := ⟨cell167,(32/11),(128/43)⟩
theorem slice167_checked : CellPartition.accepts 1 2 2 slice167=true :=
  accepts_of_checks 1 2 2 slice167 cell167_checked (by decide +kernel)
def slice168 : Slice := ⟨cell168,(128/43),(64/21)⟩
theorem slice168_checked : CellPartition.accepts 1 2 2 slice168=true :=
  accepts_of_checks 1 2 2 slice168 cell168_checked (by decide +kernel)
def slice169 : Slice := ⟨cell169,(64/21),(128/41)⟩
theorem slice169_checked : CellPartition.accepts 1 2 2 slice169=true :=
  accepts_of_checks 1 2 2 slice169 cell169_checked (by decide +kernel)
def slice170 : Slice := ⟨cell170,(128/41),(16/5)⟩
theorem slice170_checked : CellPartition.accepts 1 2 2 slice170=true :=
  accepts_of_checks 1 2 2 slice170 cell170_checked (by decide +kernel)
def slice171 : Slice := ⟨cell171,(16/5),(128/39)⟩
theorem slice171_checked : CellPartition.accepts 1 2 2 slice171=true :=
  accepts_of_checks 1 2 2 slice171 cell171_checked (by decide +kernel)
def slice172 : Slice := ⟨cell172,(128/39),(64/19)⟩
theorem slice172_checked : CellPartition.accepts 1 2 2 slice172=true :=
  accepts_of_checks 1 2 2 slice172 cell172_checked (by decide +kernel)
def slice173 : Slice := ⟨cell173,(64/19),(128/37)⟩
theorem slice173_checked : CellPartition.accepts 1 2 2 slice173=true :=
  accepts_of_checks 1 2 2 slice173 cell173_checked (by decide +kernel)
def slice174 : Slice := ⟨cell174,(128/37),(32/9)⟩
theorem slice174_checked : CellPartition.accepts 1 2 2 slice174=true :=
  accepts_of_checks 1 2 2 slice174 cell174_checked (by decide +kernel)
def slice175 : Slice := ⟨cell175,(32/9),(128/35)⟩
theorem slice175_checked : CellPartition.accepts 1 2 2 slice175=true :=
  accepts_of_checks 1 2 2 slice175 cell175_checked (by decide +kernel)
def slice176 : Slice := ⟨cell176,(128/35),(64/17)⟩
theorem slice176_checked : CellPartition.accepts 1 2 2 slice176=true :=
  accepts_of_checks 1 2 2 slice176 cell176_checked (by decide +kernel)
def slice177 : Slice := ⟨cell177,(64/17),(128/33)⟩
theorem slice177_checked : CellPartition.accepts 1 2 2 slice177=true :=
  accepts_of_checks 1 2 2 slice177 cell177_checked (by decide +kernel)
def slice178 : Slice := ⟨cell178,(128/33),(256/65)⟩
theorem slice178_checked : CellPartition.accepts 1 2 2 slice178=true :=
  accepts_of_checks 1 2 2 slice178 cell178_checked (by decide +kernel)
def slice179 : Slice := ⟨cell179,(256/65),4⟩
theorem slice179_checked : CellPartition.accepts 1 2 2 slice179=true :=
  accepts_of_checks 1 2 2 slice179 cell179_checked (by decide +kernel)
def slice180 : Slice := ⟨cell180,4,(256/63)⟩
theorem slice180_checked : CellPartition.accepts 1 2 2 slice180=true :=
  accepts_of_checks 1 2 2 slice180 cell180_checked (by decide +kernel)
def slice181 : Slice := ⟨cell181,(256/63),(128/31)⟩
theorem slice181_checked : CellPartition.accepts 1 2 2 slice181=true :=
  accepts_of_checks 1 2 2 slice181 cell181_checked (by decide +kernel)
def slice182 : Slice := ⟨cell182,(128/31),(256/61)⟩
theorem slice182_checked : CellPartition.accepts 1 2 2 slice182=true :=
  accepts_of_checks 1 2 2 slice182 cell182_checked (by decide +kernel)
def slice183 : Slice := ⟨cell183,(256/61),(64/15)⟩
theorem slice183_checked : CellPartition.accepts 1 2 2 slice183=true :=
  accepts_of_checks 1 2 2 slice183 cell183_checked (by decide +kernel)
def slice184 : Slice := ⟨cell184,(64/15),(256/59)⟩
theorem slice184_checked : CellPartition.accepts 1 2 2 slice184=true :=
  accepts_of_checks 1 2 2 slice184 cell184_checked (by decide +kernel)
def slice185 : Slice := ⟨cell185,(256/59),(128/29)⟩
theorem slice185_checked : CellPartition.accepts 1 2 2 slice185=true :=
  accepts_of_checks 1 2 2 slice185 cell185_checked (by decide +kernel)
def slice186 : Slice := ⟨cell186,(128/29),(256/57)⟩
theorem slice186_checked : CellPartition.accepts 1 2 2 slice186=true :=
  accepts_of_checks 1 2 2 slice186 cell186_checked (by decide +kernel)
def slice187 : Slice := ⟨cell187,(256/57),(32/7)⟩
theorem slice187_checked : CellPartition.accepts 1 2 2 slice187=true :=
  accepts_of_checks 1 2 2 slice187 cell187_checked (by decide +kernel)
def slice188 : Slice := ⟨cell188,(32/7),(256/55)⟩
theorem slice188_checked : CellPartition.accepts 1 2 2 slice188=true :=
  accepts_of_checks 1 2 2 slice188 cell188_checked (by decide +kernel)
def slice189 : Slice := ⟨cell189,(256/55),(128/27)⟩
theorem slice189_checked : CellPartition.accepts 1 2 2 slice189=true :=
  accepts_of_checks 1 2 2 slice189 cell189_checked (by decide +kernel)
def slice190 : Slice := ⟨cell190,(128/27),(256/53)⟩
theorem slice190_checked : CellPartition.accepts 1 2 2 slice190=true :=
  accepts_of_checks 1 2 2 slice190 cell190_checked (by decide +kernel)
def slice191 : Slice := ⟨cell191,(256/53),(64/13)⟩
theorem slice191_checked : CellPartition.accepts 1 2 2 slice191=true :=
  accepts_of_checks 1 2 2 slice191 cell191_checked (by decide +kernel)
def slice192 : Slice := ⟨cell192,(64/13),(256/51)⟩
theorem slice192_checked : CellPartition.accepts 1 2 2 slice192=true :=
  accepts_of_checks 1 2 2 slice192 cell192_checked (by decide +kernel)
def slice193 : Slice := ⟨cell193,(256/51),(128/25)⟩
theorem slice193_checked : CellPartition.accepts 1 2 2 slice193=true :=
  accepts_of_checks 1 2 2 slice193 cell193_checked (by decide +kernel)
def slice194 : Slice := ⟨cell194,(128/25),(256/49)⟩
theorem slice194_checked : CellPartition.accepts 1 2 2 slice194=true :=
  accepts_of_checks 1 2 2 slice194 cell194_checked (by decide +kernel)
def slice195 : Slice := ⟨cell195,(256/49),(16/3)⟩
theorem slice195_checked : CellPartition.accepts 1 2 2 slice195=true :=
  accepts_of_checks 1 2 2 slice195 cell195_checked (by decide +kernel)
def slice196 : Slice := ⟨cell196,(16/3),(256/47)⟩
theorem slice196_checked : CellPartition.accepts 1 2 2 slice196=true :=
  accepts_of_checks 1 2 2 slice196 cell196_checked (by decide +kernel)
def slice197 : Slice := ⟨cell197,(256/47),(128/23)⟩
theorem slice197_checked : CellPartition.accepts 1 2 2 slice197=true :=
  accepts_of_checks 1 2 2 slice197 cell197_checked (by decide +kernel)
def slice198 : Slice := ⟨cell198,(128/23),(256/45)⟩
theorem slice198_checked : CellPartition.accepts 1 2 2 slice198=true :=
  accepts_of_checks 1 2 2 slice198 cell198_checked (by decide +kernel)
def slice199 : Slice := ⟨cell199,(256/45),(64/11)⟩
theorem slice199_checked : CellPartition.accepts 1 2 2 slice199=true :=
  accepts_of_checks 1 2 2 slice199 cell199_checked (by decide +kernel)
def slice200 : Slice := ⟨cell200,(64/11),(256/43)⟩
theorem slice200_checked : CellPartition.accepts 1 2 2 slice200=true :=
  accepts_of_checks 1 2 2 slice200 cell200_checked (by decide +kernel)
def slice201 : Slice := ⟨cell201,(256/43),(128/21)⟩
theorem slice201_checked : CellPartition.accepts 1 2 2 slice201=true :=
  accepts_of_checks 1 2 2 slice201 cell201_checked (by decide +kernel)
def slice202 : Slice := ⟨cell202,(128/21),(256/41)⟩
theorem slice202_checked : CellPartition.accepts 1 2 2 slice202=true :=
  accepts_of_checks 1 2 2 slice202 cell202_checked (by decide +kernel)
def slice203 : Slice := ⟨cell203,(256/41),(32/5)⟩
theorem slice203_checked : CellPartition.accepts 1 2 2 slice203=true :=
  accepts_of_checks 1 2 2 slice203 cell203_checked (by decide +kernel)
def slice204 : Slice := ⟨cell204,(32/5),(256/39)⟩
theorem slice204_checked : CellPartition.accepts 1 2 2 slice204=true :=
  accepts_of_checks 1 2 2 slice204 cell204_checked (by decide +kernel)
def slice205 : Slice := ⟨cell205,(256/39),(128/19)⟩
theorem slice205_checked : CellPartition.accepts 1 2 2 slice205=true :=
  accepts_of_checks 1 2 2 slice205 cell205_checked (by decide +kernel)
def slice206 : Slice := ⟨cell206,(128/19),(256/37)⟩
theorem slice206_checked : CellPartition.accepts 1 2 2 slice206=true :=
  accepts_of_checks 1 2 2 slice206 cell206_checked (by decide +kernel)
def slice207 : Slice := ⟨cell207,(256/37),(64/9)⟩
theorem slice207_checked : CellPartition.accepts 1 2 2 slice207=true :=
  accepts_of_checks 1 2 2 slice207 cell207_checked (by decide +kernel)
def slice208 : Slice := ⟨cell208,(64/9),(256/35)⟩
theorem slice208_checked : CellPartition.accepts 1 2 2 slice208=true :=
  accepts_of_checks 1 2 2 slice208 cell208_checked (by decide +kernel)
def slice209 : Slice := ⟨cell209,(256/35),(128/17)⟩
theorem slice209_checked : CellPartition.accepts 1 2 2 slice209=true :=
  accepts_of_checks 1 2 2 slice209 cell209_checked (by decide +kernel)
def slice210 : Slice := ⟨cell210,(128/17),(256/33)⟩
theorem slice210_checked : CellPartition.accepts 1 2 2 slice210=true :=
  accepts_of_checks 1 2 2 slice210 cell210_checked (by decide +kernel)
def slice211 : Slice := ⟨cell211,(256/33),8⟩
theorem slice211_checked : CellPartition.accepts 1 2 2 slice211=true :=
  accepts_of_checks 1 2 2 slice211 cell211_checked (by decide +kernel)
def slice212 : Slice := ⟨cell212,8,(256/31)⟩
theorem slice212_checked : CellPartition.accepts 1 2 2 slice212=true :=
  accepts_of_checks 1 2 2 slice212 cell212_checked (by decide +kernel)
def slice213 : Slice := ⟨cell213,(256/31),(128/15)⟩
theorem slice213_checked : CellPartition.accepts 1 2 2 slice213=true :=
  accepts_of_checks 1 2 2 slice213 cell213_checked (by decide +kernel)
def slice214 : Slice := ⟨cell214,(128/15),(256/29)⟩
theorem slice214_checked : CellPartition.accepts 1 2 2 slice214=true :=
  accepts_of_checks 1 2 2 slice214 cell214_checked (by decide +kernel)
def slice215 : Slice := ⟨cell215,(256/29),(512/57)⟩
theorem slice215_checked : CellPartition.accepts 1 2 2 slice215=true :=
  accepts_of_checks 1 2 2 slice215 cell215_checked (by decide +kernel)
def slice216 : Slice := ⟨cell216,(512/57),(64/7)⟩
theorem slice216_checked : CellPartition.accepts 1 2 2 slice216=true :=
  accepts_of_checks 1 2 2 slice216 cell216_checked (by decide +kernel)
def slice217 : Slice := ⟨cell217,(64/7),(512/55)⟩
theorem slice217_checked : CellPartition.accepts 1 2 2 slice217=true :=
  accepts_of_checks 1 2 2 slice217 cell217_checked (by decide +kernel)
def slice218 : Slice := ⟨cell218,(512/55),(256/27)⟩
theorem slice218_checked : CellPartition.accepts 1 2 2 slice218=true :=
  accepts_of_checks 1 2 2 slice218 cell218_checked (by decide +kernel)
def slice219 : Slice := ⟨cell219,(256/27),(512/53)⟩
theorem slice219_checked : CellPartition.accepts 1 2 2 slice219=true :=
  accepts_of_checks 1 2 2 slice219 cell219_checked (by decide +kernel)
def slice220 : Slice := ⟨cell220,(512/53),(128/13)⟩
theorem slice220_checked : CellPartition.accepts 1 2 2 slice220=true :=
  accepts_of_checks 1 2 2 slice220 cell220_checked (by decide +kernel)
def slice221 : Slice := ⟨cell221,(128/13),(512/51)⟩
theorem slice221_checked : CellPartition.accepts 1 2 2 slice221=true :=
  accepts_of_checks 1 2 2 slice221 cell221_checked (by decide +kernel)
def slice222 : Slice := ⟨cell222,(512/51),(256/25)⟩
theorem slice222_checked : CellPartition.accepts 1 2 2 slice222=true :=
  accepts_of_checks 1 2 2 slice222 cell222_checked (by decide +kernel)
def slice223 : Slice := ⟨cell223,(256/25),(512/49)⟩
theorem slice223_checked : CellPartition.accepts 1 2 2 slice223=true :=
  accepts_of_checks 1 2 2 slice223 cell223_checked (by decide +kernel)
def slice224 : Slice := ⟨cell224,(512/49),(32/3)⟩
theorem slice224_checked : CellPartition.accepts 1 2 2 slice224=true :=
  accepts_of_checks 1 2 2 slice224 cell224_checked (by decide +kernel)
def slice225 : Slice := ⟨cell225,(32/3),(512/47)⟩
theorem slice225_checked : CellPartition.accepts 1 2 2 slice225=true :=
  accepts_of_checks 1 2 2 slice225 cell225_checked (by decide +kernel)
def slice226 : Slice := ⟨cell226,(512/47),(256/23)⟩
theorem slice226_checked : CellPartition.accepts 1 2 2 slice226=true :=
  accepts_of_checks 1 2 2 slice226 cell226_checked (by decide +kernel)
def slice227 : Slice := ⟨cell227,(256/23),(512/45)⟩
theorem slice227_checked : CellPartition.accepts 1 2 2 slice227=true :=
  accepts_of_checks 1 2 2 slice227 cell227_checked (by decide +kernel)
def slice228 : Slice := ⟨cell228,(512/45),(128/11)⟩
theorem slice228_checked : CellPartition.accepts 1 2 2 slice228=true :=
  accepts_of_checks 1 2 2 slice228 cell228_checked (by decide +kernel)
def slice229 : Slice := ⟨cell229,(128/11),(512/43)⟩
theorem slice229_checked : CellPartition.accepts 1 2 2 slice229=true :=
  accepts_of_checks 1 2 2 slice229 cell229_checked (by decide +kernel)
def slice230 : Slice := ⟨cell230,(512/43),(256/21)⟩
theorem slice230_checked : CellPartition.accepts 1 2 2 slice230=true :=
  accepts_of_checks 1 2 2 slice230 cell230_checked (by decide +kernel)
def slice231 : Slice := ⟨cell231,(256/21),(512/41)⟩
theorem slice231_checked : CellPartition.accepts 1 2 2 slice231=true :=
  accepts_of_checks 1 2 2 slice231 cell231_checked (by decide +kernel)
def slice232 : Slice := ⟨cell232,(512/41),(64/5)⟩
theorem slice232_checked : CellPartition.accepts 1 2 2 slice232=true :=
  accepts_of_checks 1 2 2 slice232 cell232_checked (by decide +kernel)
def slice233 : Slice := ⟨cell233,(64/5),(512/39)⟩
theorem slice233_checked : CellPartition.accepts 1 2 2 slice233=true :=
  accepts_of_checks 1 2 2 slice233 cell233_checked (by decide +kernel)
def slice234 : Slice := ⟨cell234,(512/39),(256/19)⟩
theorem slice234_checked : CellPartition.accepts 1 2 2 slice234=true :=
  accepts_of_checks 1 2 2 slice234 cell234_checked (by decide +kernel)
def slice235 : Slice := ⟨cell235,(256/19),(512/37)⟩
theorem slice235_checked : CellPartition.accepts 1 2 2 slice235=true :=
  accepts_of_checks 1 2 2 slice235 cell235_checked (by decide +kernel)
def slice236 : Slice := ⟨cell236,(512/37),(128/9)⟩
theorem slice236_checked : CellPartition.accepts 1 2 2 slice236=true :=
  accepts_of_checks 1 2 2 slice236 cell236_checked (by decide +kernel)
def slice237 : Slice := ⟨cell237,(128/9),(512/35)⟩
theorem slice237_checked : CellPartition.accepts 1 2 2 slice237=true :=
  accepts_of_checks 1 2 2 slice237 cell237_checked (by decide +kernel)
def slice238 : Slice := ⟨cell238,(512/35),(256/17)⟩
theorem slice238_checked : CellPartition.accepts 1 2 2 slice238=true :=
  accepts_of_checks 1 2 2 slice238 cell238_checked (by decide +kernel)
def slice239 : Slice := ⟨cell239,(256/17),(512/33)⟩
theorem slice239_checked : CellPartition.accepts 1 2 2 slice239=true :=
  accepts_of_checks 1 2 2 slice239 cell239_checked (by decide +kernel)
def slice240 : Slice := ⟨cell240,(512/33),16⟩
theorem slice240_checked : CellPartition.accepts 1 2 2 slice240=true :=
  accepts_of_checks 1 2 2 slice240 cell240_checked (by decide +kernel)
def slice241 : Slice := ⟨cell241,16,(512/31)⟩
theorem slice241_checked : CellPartition.accepts 1 2 2 slice241=true :=
  accepts_of_checks 1 2 2 slice241 cell241_checked (by decide +kernel)
def slice242 : Slice := ⟨cell242,(512/31),(256/15)⟩
theorem slice242_checked : CellPartition.accepts 1 2 2 slice242=true :=
  accepts_of_checks 1 2 2 slice242 cell242_checked (by decide +kernel)
def slice243 : Slice := ⟨cell243,(256/15),(512/29)⟩
theorem slice243_checked : CellPartition.accepts 1 2 2 slice243=true :=
  accepts_of_checks 1 2 2 slice243 cell243_checked (by decide +kernel)
def slice244 : Slice := ⟨cell244,(512/29),(128/7)⟩
theorem slice244_checked : CellPartition.accepts 1 2 2 slice244=true :=
  accepts_of_checks 1 2 2 slice244 cell244_checked (by decide +kernel)
def slice245 : Slice := ⟨cell245,(128/7),(512/27)⟩
theorem slice245_checked : CellPartition.accepts 1 2 2 slice245=true :=
  accepts_of_checks 1 2 2 slice245 cell245_checked (by decide +kernel)
def slice246 : Slice := ⟨cell246,(512/27),(256/13)⟩
theorem slice246_checked : CellPartition.accepts 1 2 2 slice246=true :=
  accepts_of_checks 1 2 2 slice246 cell246_checked (by decide +kernel)
def slice247 : Slice := ⟨cell247,(256/13),(512/25)⟩
theorem slice247_checked : CellPartition.accepts 1 2 2 slice247=true :=
  accepts_of_checks 1 2 2 slice247 cell247_checked (by decide +kernel)
def slice248 : Slice := ⟨cell248,(512/25),(64/3)⟩
theorem slice248_checked : CellPartition.accepts 1 2 2 slice248=true :=
  accepts_of_checks 1 2 2 slice248 cell248_checked (by decide +kernel)
def slice249 : Slice := ⟨cell249,(64/3),(512/23)⟩
theorem slice249_checked : CellPartition.accepts 1 2 2 slice249=true :=
  accepts_of_checks 1 2 2 slice249 cell249_checked (by decide +kernel)
def slice250 : Slice := ⟨cell250,(512/23),(256/11)⟩
theorem slice250_checked : CellPartition.accepts 1 2 2 slice250=true :=
  accepts_of_checks 1 2 2 slice250 cell250_checked (by decide +kernel)
def slice251 : Slice := ⟨cell251,(256/11),(512/21)⟩
theorem slice251_checked : CellPartition.accepts 1 2 2 slice251=true :=
  accepts_of_checks 1 2 2 slice251 cell251_checked (by decide +kernel)
def slice252 : Slice := ⟨cell252,(512/21),(128/5)⟩
theorem slice252_checked : CellPartition.accepts 1 2 2 slice252=true :=
  accepts_of_checks 1 2 2 slice252 cell252_checked (by decide +kernel)
def slice253 : Slice := ⟨cell253,(128/5),(512/19)⟩
theorem slice253_checked : CellPartition.accepts 1 2 2 slice253=true :=
  accepts_of_checks 1 2 2 slice253 cell253_checked (by decide +kernel)
def slice254 : Slice := ⟨cell254,(512/19),(256/9)⟩
theorem slice254_checked : CellPartition.accepts 1 2 2 slice254=true :=
  accepts_of_checks 1 2 2 slice254 cell254_checked (by decide +kernel)
def slice255 : Slice := ⟨cell255,(256/9),(512/17)⟩
theorem slice255_checked : CellPartition.accepts 1 2 2 slice255=true :=
  accepts_of_checks 1 2 2 slice255 cell255_checked (by decide +kernel)
def slice256 : Slice := ⟨cell256,(512/17),(1024/33)⟩
theorem slice256_checked : CellPartition.accepts 1 2 2 slice256=true :=
  accepts_of_checks 1 2 2 slice256 cell256_checked (by decide +kernel)
def slice257 : Slice := ⟨cell257,(1024/33),32⟩
theorem slice257_checked : CellPartition.accepts 1 2 2 slice257=true :=
  accepts_of_checks 1 2 2 slice257 cell257_checked (by decide +kernel)
def slice258 : Slice := ⟨cell258,32,(1024/31)⟩
theorem slice258_checked : CellPartition.accepts 1 2 2 slice258=true :=
  accepts_of_checks 1 2 2 slice258 cell258_checked (by decide +kernel)
def slice259 : Slice := ⟨cell259,(1024/31),(512/15)⟩
theorem slice259_checked : CellPartition.accepts 1 2 2 slice259=true :=
  accepts_of_checks 1 2 2 slice259 cell259_checked (by decide +kernel)
def slice260 : Slice := ⟨cell260,(512/15),(1024/29)⟩
theorem slice260_checked : CellPartition.accepts 1 2 2 slice260=true :=
  accepts_of_checks 1 2 2 slice260 cell260_checked (by decide +kernel)
def slice261 : Slice := ⟨cell261,(1024/29),(256/7)⟩
theorem slice261_checked : CellPartition.accepts 1 2 2 slice261=true :=
  accepts_of_checks 1 2 2 slice261 cell261_checked (by decide +kernel)
def slice262 : Slice := ⟨cell262,(256/7),(1024/27)⟩
theorem slice262_checked : CellPartition.accepts 1 2 2 slice262=true :=
  accepts_of_checks 1 2 2 slice262 cell262_checked (by decide +kernel)
def slice263 : Slice := ⟨cell263,(1024/27),(512/13)⟩
theorem slice263_checked : CellPartition.accepts 1 2 2 slice263=true :=
  accepts_of_checks 1 2 2 slice263 cell263_checked (by decide +kernel)
def slice264 : Slice := ⟨cell264,(512/13),(1024/25)⟩
theorem slice264_checked : CellPartition.accepts 1 2 2 slice264=true :=
  accepts_of_checks 1 2 2 slice264 cell264_checked (by decide +kernel)
def slice265 : Slice := ⟨cell265,(1024/25),(128/3)⟩
theorem slice265_checked : CellPartition.accepts 1 2 2 slice265=true :=
  accepts_of_checks 1 2 2 slice265 cell265_checked (by decide +kernel)
def slice266 : Slice := ⟨cell266,(128/3),(1024/23)⟩
theorem slice266_checked : CellPartition.accepts 1 2 2 slice266=true :=
  accepts_of_checks 1 2 2 slice266 cell266_checked (by decide +kernel)
def slice267 : Slice := ⟨cell267,(1024/23),(512/11)⟩
theorem slice267_checked : CellPartition.accepts 1 2 2 slice267=true :=
  accepts_of_checks 1 2 2 slice267 cell267_checked (by decide +kernel)
def slice268 : Slice := ⟨cell268,(512/11),(1024/21)⟩
theorem slice268_checked : CellPartition.accepts 1 2 2 slice268=true :=
  accepts_of_checks 1 2 2 slice268 cell268_checked (by decide +kernel)
def slice269 : Slice := ⟨cell269,(1024/21),(256/5)⟩
theorem slice269_checked : CellPartition.accepts 1 2 2 slice269=true :=
  accepts_of_checks 1 2 2 slice269 cell269_checked (by decide +kernel)
def slice270 : Slice := ⟨cell270,(256/5),(1024/19)⟩
theorem slice270_checked : CellPartition.accepts 1 2 2 slice270=true :=
  accepts_of_checks 1 2 2 slice270 cell270_checked (by decide +kernel)
def slice271 : Slice := ⟨cell271,(1024/19),(512/9)⟩
theorem slice271_checked : CellPartition.accepts 1 2 2 slice271=true :=
  accepts_of_checks 1 2 2 slice271 cell271_checked (by decide +kernel)
def slice272 : Slice := ⟨cell272,(512/9),(1024/17)⟩
theorem slice272_checked : CellPartition.accepts 1 2 2 slice272=true :=
  accepts_of_checks 1 2 2 slice272 cell272_checked (by decide +kernel)
def slice273 : Slice := ⟨cell273,(1024/17),64⟩
theorem slice273_checked : CellPartition.accepts 1 2 2 slice273=true :=
  accepts_of_checks 1 2 2 slice273 cell273_checked (by decide +kernel)
def slice274 : Slice := ⟨cell274,64,(1024/15)⟩
theorem slice274_checked : CellPartition.accepts 1 2 2 slice274=true :=
  accepts_of_checks 1 2 2 slice274 cell274_checked (by decide +kernel)
def slice275 : Slice := ⟨cell275,(1024/15),(512/7)⟩
theorem slice275_checked : CellPartition.accepts 1 2 2 slice275=true :=
  accepts_of_checks 1 2 2 slice275 cell275_checked (by decide +kernel)
def slice276 : Slice := ⟨cell276,(512/7),(1024/13)⟩
theorem slice276_checked : CellPartition.accepts 1 2 2 slice276=true :=
  accepts_of_checks 1 2 2 slice276 cell276_checked (by decide +kernel)
def slice277 : Slice := ⟨cell277,(1024/13),(256/3)⟩
theorem slice277_checked : CellPartition.accepts 1 2 2 slice277=true :=
  accepts_of_checks 1 2 2 slice277 cell277_checked (by decide +kernel)
def slice278 : Slice := ⟨cell278,(256/3),(1024/11)⟩
theorem slice278_checked : CellPartition.accepts 1 2 2 slice278=true :=
  accepts_of_checks 1 2 2 slice278 cell278_checked (by decide +kernel)
def slice279 : Slice := ⟨cell279,(1024/11),(512/5)⟩
theorem slice279_checked : CellPartition.accepts 1 2 2 slice279=true :=
  accepts_of_checks 1 2 2 slice279 cell279_checked (by decide +kernel)
def slice280 : Slice := ⟨cell280,(512/5),(1024/9)⟩
theorem slice280_checked : CellPartition.accepts 1 2 2 slice280=true :=
  accepts_of_checks 1 2 2 slice280 cell280_checked (by decide +kernel)
def slice281 : Slice := ⟨cell281,(1024/9),(2048/17)⟩
theorem slice281_checked : CellPartition.accepts 1 2 2 slice281=true :=
  accepts_of_checks 1 2 2 slice281 cell281_checked (by decide +kernel)
def slice282 : Slice := ⟨cell282,(2048/17),128⟩
theorem slice282_checked : CellPartition.accepts 1 2 2 slice282=true :=
  accepts_of_checks 1 2 2 slice282 cell282_checked (by decide +kernel)
def slice283 : Slice := ⟨cell283,128,(2048/15)⟩
theorem slice283_checked : CellPartition.accepts 1 2 2 slice283=true :=
  accepts_of_checks 1 2 2 slice283 cell283_checked (by decide +kernel)
def slice284 : Slice := ⟨cell284,(2048/15),(1024/7)⟩
theorem slice284_checked : CellPartition.accepts 1 2 2 slice284=true :=
  accepts_of_checks 1 2 2 slice284 cell284_checked (by decide +kernel)
def slice285 : Slice := ⟨cell285,(1024/7),(2048/13)⟩
theorem slice285_checked : CellPartition.accepts 1 2 2 slice285=true :=
  accepts_of_checks 1 2 2 slice285 cell285_checked (by decide +kernel)
def slice286 : Slice := ⟨cell286,(2048/13),(512/3)⟩
theorem slice286_checked : CellPartition.accepts 1 2 2 slice286=true :=
  accepts_of_checks 1 2 2 slice286 cell286_checked (by decide +kernel)
def slice287 : Slice := ⟨cell287,(512/3),(2048/11)⟩
theorem slice287_checked : CellPartition.accepts 1 2 2 slice287=true :=
  accepts_of_checks 1 2 2 slice287 cell287_checked (by decide +kernel)
def slice288 : Slice := ⟨cell288,(2048/11),(1024/5)⟩
theorem slice288_checked : CellPartition.accepts 1 2 2 slice288=true :=
  accepts_of_checks 1 2 2 slice288 cell288_checked (by decide +kernel)
def slice289 : Slice := ⟨cell289,(1024/5),(2048/9)⟩
theorem slice289_checked : CellPartition.accepts 1 2 2 slice289=true :=
  accepts_of_checks 1 2 2 slice289 cell289_checked (by decide +kernel)
def slice290 : Slice := ⟨cell290,(2048/9),256⟩
theorem slice290_checked : CellPartition.accepts 1 2 2 slice290=true :=
  accepts_of_checks 1 2 2 slice290 cell290_checked (by decide +kernel)
def slice291 : Slice := ⟨cell291,256,(2048/7)⟩
theorem slice291_checked : CellPartition.accepts 1 2 2 slice291=true :=
  accepts_of_checks 1 2 2 slice291 cell291_checked (by decide +kernel)
def slice292 : Slice := ⟨cell292,(2048/7),(1024/3)⟩
theorem slice292_checked : CellPartition.accepts 1 2 2 slice292=true :=
  accepts_of_checks 1 2 2 slice292 cell292_checked (by decide +kernel)
def slice293 : Slice := ⟨cell293,(1024/3),(2048/5)⟩
theorem slice293_checked : CellPartition.accepts 1 2 2 slice293=true :=
  accepts_of_checks 1 2 2 slice293 cell293_checked (by decide +kernel)
def slice294 : Slice := ⟨cell294,(2048/5),512⟩
theorem slice294_checked : CellPartition.accepts 1 2 2 slice294=true :=
  accepts_of_checks 1 2 2 slice294 cell294_checked (by decide +kernel)
def slice295 : Slice := ⟨cell295,512,(4096/7)⟩
theorem slice295_checked : CellPartition.accepts 1 2 2 slice295=true :=
  accepts_of_checks 1 2 2 slice295 cell295_checked (by decide +kernel)
def slice296 : Slice := ⟨cell296,(4096/7),(2048/3)⟩
theorem slice296_checked : CellPartition.accepts 1 2 2 slice296=true :=
  accepts_of_checks 1 2 2 slice296 cell296_checked (by decide +kernel)
def slice297 : Slice := ⟨cell297,(2048/3),(4096/5)⟩
theorem slice297_checked : CellPartition.accepts 1 2 2 slice297=true :=
  accepts_of_checks 1 2 2 slice297 cell297_checked (by decide +kernel)
def slice298 : Slice := ⟨cell298,(4096/5),1024⟩
theorem slice298_checked : CellPartition.accepts 1 2 2 slice298=true :=
  accepts_of_checks 1 2 2 slice298 cell298_checked (by decide +kernel)
def partition : List Slice := [slice000,slice001,slice002,slice003,slice004,slice005,slice006,slice007,slice008,slice009,slice010,slice011,slice012,slice013,slice014,slice015,slice016,slice017,slice018,slice019,slice020,slice021,slice022,slice023,slice024,slice025,slice026,slice027,slice028,slice029,slice030,slice031,slice032,slice033,slice034,slice035,slice036,slice037,slice038,slice039,slice040,slice041,slice042,slice043,slice044,slice045,slice046,slice047,slice048,slice049,slice050,slice051,slice052,slice053,slice054,slice055,slice056,slice057,slice058,slice059,slice060,slice061,slice062,slice063,slice064,slice065,slice066,slice067,slice068,slice069,slice070,slice071,slice072,slice073,slice074,slice075,slice076,slice077,slice078,slice079,slice080,slice081,slice082,slice083,slice084,slice085,slice086,slice087,slice088,slice089,slice090,slice091,slice092,slice093,slice094,slice095,slice096,slice097,slice098,slice099,slice100,slice101,slice102,slice103,slice104,slice105,slice106,slice107,slice108,slice109,slice110,slice111,slice112,slice113,slice114,slice115,slice116,slice117,slice118,slice119,slice120,slice121,slice122,slice123,slice124,slice125,slice126,slice127,slice128,slice129,slice130,slice131,slice132,slice133,slice134,slice135,slice136,slice137,slice138,slice139,slice140,slice141,slice142,slice143,slice144,slice145,slice146,slice147,slice148,slice149,slice150,slice151,slice152,slice153,slice154,slice155,slice156,slice157,slice158,slice159,slice160,slice161,slice162,slice163,slice164,slice165,slice166,slice167,slice168,slice169,slice170,slice171,slice172,slice173,slice174,slice175,slice176,slice177,slice178,slice179,slice180,slice181,slice182,slice183,slice184,slice185,slice186,slice187,slice188,slice189,slice190,slice191,slice192,slice193,slice194,slice195,slice196,slice197,slice198,slice199,slice200,slice201,slice202,slice203,slice204,slice205,slice206,slice207,slice208,slice209,slice210,slice211,slice212,slice213,slice214,slice215,slice216,slice217,slice218,slice219,slice220,slice221,slice222,slice223,slice224,slice225,slice226,slice227,slice228,slice229,slice230,slice231,slice232,slice233,slice234,slice235,slice236,slice237,slice238,slice239,slice240,slice241,slice242,slice243,slice244,slice245,slice246,slice247,slice248,slice249,slice250,slice251,slice252,slice253,slice254,slice255,slice256,slice257,slice258,slice259,slice260,slice261,slice262,slice263,slice264,slice265,slice266,slice267,slice268,slice269,slice270,slice271,slice272,slice273,slice274,slice275,slice276,slice277,slice278,slice279,slice280,slice281,slice282,slice283,slice284,slice285,slice286,slice287,slice288,slice289,slice290,slice291,slice292,slice293,slice294,slice295,slice296,slice297,slice298]
theorem partition_checked : checkAt 1 2 2 (1/1000) 1024 partition=true := by
  unfold partition
  apply checked_cons _ _ _ _ _ _ _ rfl slice000_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice001_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice002_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice003_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice004_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice005_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice006_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice007_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice008_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice009_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice010_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice011_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice012_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice013_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice014_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice015_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice016_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice017_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice018_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice019_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice020_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice021_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice022_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice023_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice024_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice025_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice026_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice027_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice028_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice029_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice030_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice031_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice032_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice033_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice034_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice035_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice036_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice037_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice038_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice039_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice040_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice041_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice042_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice043_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice044_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice045_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice046_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice047_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice048_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice049_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice050_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice051_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice052_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice053_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice054_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice055_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice056_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice057_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice058_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice059_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice060_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice061_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice062_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice063_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice064_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice065_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice066_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice067_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice068_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice069_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice070_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice071_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice072_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice073_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice074_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice075_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice076_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice077_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice078_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice079_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice080_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice081_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice082_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice083_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice084_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice085_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice086_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice087_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice088_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice089_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice090_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice091_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice092_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice093_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice094_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice095_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice096_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice097_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice098_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice099_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice100_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice101_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice102_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice103_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice104_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice105_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice106_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice107_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice108_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice109_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice110_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice111_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice112_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice113_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice114_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice115_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice116_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice117_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice118_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice119_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice120_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice121_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice122_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice123_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice124_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice125_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice126_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice127_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice128_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice129_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice130_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice131_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice132_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice133_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice134_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice135_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice136_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice137_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice138_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice139_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice140_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice141_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice142_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice143_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice144_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice145_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice146_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice147_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice148_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice149_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice150_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice151_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice152_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice153_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice154_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice155_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice156_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice157_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice158_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice159_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice160_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice161_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice162_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice163_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice164_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice165_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice166_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice167_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice168_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice169_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice170_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice171_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice172_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice173_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice174_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice175_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice176_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice177_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice178_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice179_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice180_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice181_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice182_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice183_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice184_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice185_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice186_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice187_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice188_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice189_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice190_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice191_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice192_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice193_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice194_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice195_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice196_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice197_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice198_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice199_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice200_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice201_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice202_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice203_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice204_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice205_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice206_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice207_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice208_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice209_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice210_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice211_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice212_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice213_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice214_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice215_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice216_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice217_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice218_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice219_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice220_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice221_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice222_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice223_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice224_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice225_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice226_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice227_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice228_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice229_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice230_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice231_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice232_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice233_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice234_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice235_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice236_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice237_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice238_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice239_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice240_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice241_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice242_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice243_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice244_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice245_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice246_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice247_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice248_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice249_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice250_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice251_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice252_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice253_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice254_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice255_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice256_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice257_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice258_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice259_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice260_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice261_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice262_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice263_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice264_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice265_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice266_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice267_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice268_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice269_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice270_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice271_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice272_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice273_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice274_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice275_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice276_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice277_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice278_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice279_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice280_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice281_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice282_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice283_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice284_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice285_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice286_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice287_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice288_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice289_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice290_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice291_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice292_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice293_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice294_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice295_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice296_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice297_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice298_checked
  decide +kernel
theorem budget_checked : PaidDegreeOneClass.accepts (payment partition)=true := by decide +kernel
noncomputable section
open scoped Classical
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=2) (hq : ArmClasses.classify q=2) :
    (189/5000 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 :=
  PaidDegreeOneClass.normalized_target C u p q hd 2 2 hp hq
    partition partition_checked budget_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.DegreeOneShortClass33
