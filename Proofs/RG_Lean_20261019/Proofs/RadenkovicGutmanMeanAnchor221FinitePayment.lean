/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch000
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch001
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch002
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch003
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch004
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch005
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch006
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch007
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch008
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch009
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch010
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch011
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch012
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch013
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch014
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch015
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch016
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch017
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch018
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch019
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch020
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch021
import Proofs.RadenkovicGutmanMeanAnchor221FastBatch022
import Proofs.RadenkovicGutmanRationalIntegralPartition

namespace Gebendorfer.RadenkovicGutman.MeanAnchor221FinitePayment
open Set MeasureTheory RationalIntegralPartition
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def slices : List Slice := [
  ⟨MeanAnchor221FastPolynomialCell000.cell.a,MeanAnchor221FastPolynomialCell000.cell.b,MeanAnchor221FastPolynomialCell000.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell001.cell.a,MeanAnchor221FastPolynomialCell001.cell.b,MeanAnchor221FastPolynomialCell001.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell002.cell.a,MeanAnchor221FastPolynomialCell002.cell.b,MeanAnchor221FastPolynomialCell002.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell003.cell.a,MeanAnchor221FastPolynomialCell003.cell.b,MeanAnchor221FastPolynomialCell003.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell004.cell.a,MeanAnchor221FastPolynomialCell004.cell.b,MeanAnchor221FastPolynomialCell004.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell005.cell.a,MeanAnchor221FastPolynomialCell005.cell.b,MeanAnchor221FastPolynomialCell005.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell006.cell.a,MeanAnchor221FastPolynomialCell006.cell.b,MeanAnchor221FastPolynomialCell006.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell007.cell.a,MeanAnchor221FastPolynomialCell007.cell.b,MeanAnchor221FastPolynomialCell007.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell008.cell.a,MeanAnchor221FastPolynomialCell008.cell.b,MeanAnchor221FastPolynomialCell008.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell009.cell.a,MeanAnchor221FastPolynomialCell009.cell.b,MeanAnchor221FastPolynomialCell009.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell010.cell.a,MeanAnchor221FastPolynomialCell010.cell.b,MeanAnchor221FastPolynomialCell010.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell011.cell.a,MeanAnchor221FastPolynomialCell011.cell.b,MeanAnchor221FastPolynomialCell011.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell012.cell.a,MeanAnchor221FastPolynomialCell012.cell.b,MeanAnchor221FastPolynomialCell012.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell013.cell.a,MeanAnchor221FastPolynomialCell013.cell.b,MeanAnchor221FastPolynomialCell013.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell014.cell.a,MeanAnchor221FastPolynomialCell014.cell.b,MeanAnchor221FastPolynomialCell014.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell015.cell.a,MeanAnchor221FastPolynomialCell015.cell.b,MeanAnchor221FastPolynomialCell015.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell016.cell.a,MeanAnchor221FastPolynomialCell016.cell.b,MeanAnchor221FastPolynomialCell016.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell017.cell.a,MeanAnchor221FastPolynomialCell017.cell.b,MeanAnchor221FastPolynomialCell017.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell018.cell.a,MeanAnchor221FastPolynomialCell018.cell.b,MeanAnchor221FastPolynomialCell018.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell019.cell.a,MeanAnchor221FastPolynomialCell019.cell.b,MeanAnchor221FastPolynomialCell019.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell020.cell.a,MeanAnchor221FastPolynomialCell020.cell.b,MeanAnchor221FastPolynomialCell020.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell021.cell.a,MeanAnchor221FastPolynomialCell021.cell.b,MeanAnchor221FastPolynomialCell021.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell022.cell.a,MeanAnchor221FastPolynomialCell022.cell.b,MeanAnchor221FastPolynomialCell022.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell023.cell.a,MeanAnchor221FastPolynomialCell023.cell.b,MeanAnchor221FastPolynomialCell023.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell024.cell.a,MeanAnchor221FastPolynomialCell024.cell.b,MeanAnchor221FastPolynomialCell024.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell025.cell.a,MeanAnchor221FastPolynomialCell025.cell.b,MeanAnchor221FastPolynomialCell025.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell026.cell.a,MeanAnchor221FastPolynomialCell026.cell.b,MeanAnchor221FastPolynomialCell026.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell027.cell.a,MeanAnchor221FastPolynomialCell027.cell.b,MeanAnchor221FastPolynomialCell027.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell028.cell.a,MeanAnchor221FastPolynomialCell028.cell.b,MeanAnchor221FastPolynomialCell028.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell029.cell.a,MeanAnchor221FastPolynomialCell029.cell.b,MeanAnchor221FastPolynomialCell029.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell030.cell.a,MeanAnchor221FastPolynomialCell030.cell.b,MeanAnchor221FastPolynomialCell030.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell031.cell.a,MeanAnchor221FastPolynomialCell031.cell.b,MeanAnchor221FastPolynomialCell031.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell032.cell.a,MeanAnchor221FastPolynomialCell032.cell.b,MeanAnchor221FastPolynomialCell032.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell033.cell.a,MeanAnchor221FastPolynomialCell033.cell.b,MeanAnchor221FastPolynomialCell033.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell034.cell.a,MeanAnchor221FastPolynomialCell034.cell.b,MeanAnchor221FastPolynomialCell034.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell035.cell.a,MeanAnchor221FastPolynomialCell035.cell.b,MeanAnchor221FastPolynomialCell035.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell036.cell.a,MeanAnchor221FastPolynomialCell036.cell.b,MeanAnchor221FastPolynomialCell036.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell037.cell.a,MeanAnchor221FastPolynomialCell037.cell.b,MeanAnchor221FastPolynomialCell037.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell038.cell.a,MeanAnchor221FastPolynomialCell038.cell.b,MeanAnchor221FastPolynomialCell038.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell039.cell.a,MeanAnchor221FastPolynomialCell039.cell.b,MeanAnchor221FastPolynomialCell039.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell040.cell.a,MeanAnchor221FastPolynomialCell040.cell.b,MeanAnchor221FastPolynomialCell040.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell041.cell.a,MeanAnchor221FastPolynomialCell041.cell.b,MeanAnchor221FastPolynomialCell041.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell042.cell.a,MeanAnchor221FastPolynomialCell042.cell.b,MeanAnchor221FastPolynomialCell042.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell043.cell.a,MeanAnchor221FastPolynomialCell043.cell.b,MeanAnchor221FastPolynomialCell043.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell044.cell.a,MeanAnchor221FastPolynomialCell044.cell.b,MeanAnchor221FastPolynomialCell044.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell045.cell.a,MeanAnchor221FastPolynomialCell045.cell.b,MeanAnchor221FastPolynomialCell045.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell046.cell.a,MeanAnchor221FastPolynomialCell046.cell.b,MeanAnchor221FastPolynomialCell046.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell047.cell.a,MeanAnchor221FastPolynomialCell047.cell.b,MeanAnchor221FastPolynomialCell047.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell048.cell.a,MeanAnchor221FastPolynomialCell048.cell.b,MeanAnchor221FastPolynomialCell048.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell049.cell.a,MeanAnchor221FastPolynomialCell049.cell.b,MeanAnchor221FastPolynomialCell049.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell050.cell.a,MeanAnchor221FastPolynomialCell050.cell.b,MeanAnchor221FastPolynomialCell050.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell051.cell.a,MeanAnchor221FastPolynomialCell051.cell.b,MeanAnchor221FastPolynomialCell051.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell052.cell.a,MeanAnchor221FastPolynomialCell052.cell.b,MeanAnchor221FastPolynomialCell052.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell053.cell.a,MeanAnchor221FastPolynomialCell053.cell.b,MeanAnchor221FastPolynomialCell053.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell054.cell.a,MeanAnchor221FastPolynomialCell054.cell.b,MeanAnchor221FastPolynomialCell054.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell055.cell.a,MeanAnchor221FastPolynomialCell055.cell.b,MeanAnchor221FastPolynomialCell055.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell056.cell.a,MeanAnchor221FastPolynomialCell056.cell.b,MeanAnchor221FastPolynomialCell056.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell057.cell.a,MeanAnchor221FastPolynomialCell057.cell.b,MeanAnchor221FastPolynomialCell057.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell058.cell.a,MeanAnchor221FastPolynomialCell058.cell.b,MeanAnchor221FastPolynomialCell058.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell059.cell.a,MeanAnchor221FastPolynomialCell059.cell.b,MeanAnchor221FastPolynomialCell059.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell060.cell.a,MeanAnchor221FastPolynomialCell060.cell.b,MeanAnchor221FastPolynomialCell060.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell061.cell.a,MeanAnchor221FastPolynomialCell061.cell.b,MeanAnchor221FastPolynomialCell061.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell062.cell.a,MeanAnchor221FastPolynomialCell062.cell.b,MeanAnchor221FastPolynomialCell062.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell063.cell.a,MeanAnchor221FastPolynomialCell063.cell.b,MeanAnchor221FastPolynomialCell063.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell064.cell.a,MeanAnchor221FastPolynomialCell064.cell.b,MeanAnchor221FastPolynomialCell064.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell065.cell.a,MeanAnchor221FastPolynomialCell065.cell.b,MeanAnchor221FastPolynomialCell065.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell066.cell.a,MeanAnchor221FastPolynomialCell066.cell.b,MeanAnchor221FastPolynomialCell066.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell067.cell.a,MeanAnchor221FastPolynomialCell067.cell.b,MeanAnchor221FastPolynomialCell067.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell068.cell.a,MeanAnchor221FastPolynomialCell068.cell.b,MeanAnchor221FastPolynomialCell068.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell069.cell.a,MeanAnchor221FastPolynomialCell069.cell.b,MeanAnchor221FastPolynomialCell069.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell070.cell.a,MeanAnchor221FastPolynomialCell070.cell.b,MeanAnchor221FastPolynomialCell070.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell071.cell.a,MeanAnchor221FastPolynomialCell071.cell.b,MeanAnchor221FastPolynomialCell071.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell072.cell.a,MeanAnchor221FastPolynomialCell072.cell.b,MeanAnchor221FastPolynomialCell072.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell073.cell.a,MeanAnchor221FastPolynomialCell073.cell.b,MeanAnchor221FastPolynomialCell073.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell074.cell.a,MeanAnchor221FastPolynomialCell074.cell.b,MeanAnchor221FastPolynomialCell074.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell075.cell.a,MeanAnchor221FastPolynomialCell075.cell.b,MeanAnchor221FastPolynomialCell075.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell076.cell.a,MeanAnchor221FastPolynomialCell076.cell.b,MeanAnchor221FastPolynomialCell076.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell077.cell.a,MeanAnchor221FastPolynomialCell077.cell.b,MeanAnchor221FastPolynomialCell077.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell078.cell.a,MeanAnchor221FastPolynomialCell078.cell.b,MeanAnchor221FastPolynomialCell078.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell079.cell.a,MeanAnchor221FastPolynomialCell079.cell.b,MeanAnchor221FastPolynomialCell079.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell080.cell.a,MeanAnchor221FastPolynomialCell080.cell.b,MeanAnchor221FastPolynomialCell080.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell081.cell.a,MeanAnchor221FastPolynomialCell081.cell.b,MeanAnchor221FastPolynomialCell081.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell082.cell.a,MeanAnchor221FastPolynomialCell082.cell.b,MeanAnchor221FastPolynomialCell082.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell083.cell.a,MeanAnchor221FastPolynomialCell083.cell.b,MeanAnchor221FastPolynomialCell083.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell084.cell.a,MeanAnchor221FastPolynomialCell084.cell.b,MeanAnchor221FastPolynomialCell084.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell085.cell.a,MeanAnchor221FastPolynomialCell085.cell.b,MeanAnchor221FastPolynomialCell085.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell086.cell.a,MeanAnchor221FastPolynomialCell086.cell.b,MeanAnchor221FastPolynomialCell086.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell087.cell.a,MeanAnchor221FastPolynomialCell087.cell.b,MeanAnchor221FastPolynomialCell087.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell088.cell.a,MeanAnchor221FastPolynomialCell088.cell.b,MeanAnchor221FastPolynomialCell088.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell089.cell.a,MeanAnchor221FastPolynomialCell089.cell.b,MeanAnchor221FastPolynomialCell089.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell090.cell.a,MeanAnchor221FastPolynomialCell090.cell.b,MeanAnchor221FastPolynomialCell090.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell091.cell.a,MeanAnchor221FastPolynomialCell091.cell.b,MeanAnchor221FastPolynomialCell091.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell092.cell.a,MeanAnchor221FastPolynomialCell092.cell.b,MeanAnchor221FastPolynomialCell092.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell093.cell.a,MeanAnchor221FastPolynomialCell093.cell.b,MeanAnchor221FastPolynomialCell093.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell094.cell.a,MeanAnchor221FastPolynomialCell094.cell.b,MeanAnchor221FastPolynomialCell094.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell095.cell.a,MeanAnchor221FastPolynomialCell095.cell.b,MeanAnchor221FastPolynomialCell095.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell096.cell.a,MeanAnchor221FastPolynomialCell096.cell.b,MeanAnchor221FastPolynomialCell096.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell097.cell.a,MeanAnchor221FastPolynomialCell097.cell.b,MeanAnchor221FastPolynomialCell097.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell098.cell.a,MeanAnchor221FastPolynomialCell098.cell.b,MeanAnchor221FastPolynomialCell098.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell099.cell.a,MeanAnchor221FastPolynomialCell099.cell.b,MeanAnchor221FastPolynomialCell099.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell100.cell.a,MeanAnchor221FastPolynomialCell100.cell.b,MeanAnchor221FastPolynomialCell100.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell101.cell.a,MeanAnchor221FastPolynomialCell101.cell.b,MeanAnchor221FastPolynomialCell101.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell102.cell.a,MeanAnchor221FastPolynomialCell102.cell.b,MeanAnchor221FastPolynomialCell102.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell103.cell.a,MeanAnchor221FastPolynomialCell103.cell.b,MeanAnchor221FastPolynomialCell103.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell104.cell.a,MeanAnchor221FastPolynomialCell104.cell.b,MeanAnchor221FastPolynomialCell104.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell105.cell.a,MeanAnchor221FastPolynomialCell105.cell.b,MeanAnchor221FastPolynomialCell105.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell106.cell.a,MeanAnchor221FastPolynomialCell106.cell.b,MeanAnchor221FastPolynomialCell106.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell107.cell.a,MeanAnchor221FastPolynomialCell107.cell.b,MeanAnchor221FastPolynomialCell107.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell108.cell.a,MeanAnchor221FastPolynomialCell108.cell.b,MeanAnchor221FastPolynomialCell108.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell109.cell.a,MeanAnchor221FastPolynomialCell109.cell.b,MeanAnchor221FastPolynomialCell109.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell110.cell.a,MeanAnchor221FastPolynomialCell110.cell.b,MeanAnchor221FastPolynomialCell110.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell111.cell.a,MeanAnchor221FastPolynomialCell111.cell.b,MeanAnchor221FastPolynomialCell111.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell112.cell.a,MeanAnchor221FastPolynomialCell112.cell.b,MeanAnchor221FastPolynomialCell112.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell113.cell.a,MeanAnchor221FastPolynomialCell113.cell.b,MeanAnchor221FastPolynomialCell113.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell114.cell.a,MeanAnchor221FastPolynomialCell114.cell.b,MeanAnchor221FastPolynomialCell114.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell115.cell.a,MeanAnchor221FastPolynomialCell115.cell.b,MeanAnchor221FastPolynomialCell115.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell116.cell.a,MeanAnchor221FastPolynomialCell116.cell.b,MeanAnchor221FastPolynomialCell116.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell117.cell.a,MeanAnchor221FastPolynomialCell117.cell.b,MeanAnchor221FastPolynomialCell117.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell118.cell.a,MeanAnchor221FastPolynomialCell118.cell.b,MeanAnchor221FastPolynomialCell118.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell119.cell.a,MeanAnchor221FastPolynomialCell119.cell.b,MeanAnchor221FastPolynomialCell119.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell120.cell.a,MeanAnchor221FastPolynomialCell120.cell.b,MeanAnchor221FastPolynomialCell120.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell121.cell.a,MeanAnchor221FastPolynomialCell121.cell.b,MeanAnchor221FastPolynomialCell121.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell122.cell.a,MeanAnchor221FastPolynomialCell122.cell.b,MeanAnchor221FastPolynomialCell122.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell123.cell.a,MeanAnchor221FastPolynomialCell123.cell.b,MeanAnchor221FastPolynomialCell123.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell124.cell.a,MeanAnchor221FastPolynomialCell124.cell.b,MeanAnchor221FastPolynomialCell124.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell125.cell.a,MeanAnchor221FastPolynomialCell125.cell.b,MeanAnchor221FastPolynomialCell125.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell126.cell.a,MeanAnchor221FastPolynomialCell126.cell.b,MeanAnchor221FastPolynomialCell126.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell127.cell.a,MeanAnchor221FastPolynomialCell127.cell.b,MeanAnchor221FastPolynomialCell127.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell128.cell.a,MeanAnchor221FastPolynomialCell128.cell.b,MeanAnchor221FastPolynomialCell128.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell129.cell.a,MeanAnchor221FastPolynomialCell129.cell.b,MeanAnchor221FastPolynomialCell129.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell130.cell.a,MeanAnchor221FastPolynomialCell130.cell.b,MeanAnchor221FastPolynomialCell130.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell131.cell.a,MeanAnchor221FastPolynomialCell131.cell.b,MeanAnchor221FastPolynomialCell131.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell132.cell.a,MeanAnchor221FastPolynomialCell132.cell.b,MeanAnchor221FastPolynomialCell132.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell133.cell.a,MeanAnchor221FastPolynomialCell133.cell.b,MeanAnchor221FastPolynomialCell133.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell134.cell.a,MeanAnchor221FastPolynomialCell134.cell.b,MeanAnchor221FastPolynomialCell134.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell135.cell.a,MeanAnchor221FastPolynomialCell135.cell.b,MeanAnchor221FastPolynomialCell135.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell136.cell.a,MeanAnchor221FastPolynomialCell136.cell.b,MeanAnchor221FastPolynomialCell136.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell137.cell.a,MeanAnchor221FastPolynomialCell137.cell.b,MeanAnchor221FastPolynomialCell137.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell138.cell.a,MeanAnchor221FastPolynomialCell138.cell.b,MeanAnchor221FastPolynomialCell138.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell139.cell.a,MeanAnchor221FastPolynomialCell139.cell.b,MeanAnchor221FastPolynomialCell139.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell140.cell.a,MeanAnchor221FastPolynomialCell140.cell.b,MeanAnchor221FastPolynomialCell140.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell141.cell.a,MeanAnchor221FastPolynomialCell141.cell.b,MeanAnchor221FastPolynomialCell141.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell142.cell.a,MeanAnchor221FastPolynomialCell142.cell.b,MeanAnchor221FastPolynomialCell142.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell143.cell.a,MeanAnchor221FastPolynomialCell143.cell.b,MeanAnchor221FastPolynomialCell143.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell144.cell.a,MeanAnchor221FastPolynomialCell144.cell.b,MeanAnchor221FastPolynomialCell144.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell145.cell.a,MeanAnchor221FastPolynomialCell145.cell.b,MeanAnchor221FastPolynomialCell145.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell146.cell.a,MeanAnchor221FastPolynomialCell146.cell.b,MeanAnchor221FastPolynomialCell146.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell147.cell.a,MeanAnchor221FastPolynomialCell147.cell.b,MeanAnchor221FastPolynomialCell147.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell148.cell.a,MeanAnchor221FastPolynomialCell148.cell.b,MeanAnchor221FastPolynomialCell148.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell149.cell.a,MeanAnchor221FastPolynomialCell149.cell.b,MeanAnchor221FastPolynomialCell149.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell150.cell.a,MeanAnchor221FastPolynomialCell150.cell.b,MeanAnchor221FastPolynomialCell150.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell151.cell.a,MeanAnchor221FastPolynomialCell151.cell.b,MeanAnchor221FastPolynomialCell151.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell152.cell.a,MeanAnchor221FastPolynomialCell152.cell.b,MeanAnchor221FastPolynomialCell152.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell153.cell.a,MeanAnchor221FastPolynomialCell153.cell.b,MeanAnchor221FastPolynomialCell153.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell154.cell.a,MeanAnchor221FastPolynomialCell154.cell.b,MeanAnchor221FastPolynomialCell154.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell155.cell.a,MeanAnchor221FastPolynomialCell155.cell.b,MeanAnchor221FastPolynomialCell155.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell156.cell.a,MeanAnchor221FastPolynomialCell156.cell.b,MeanAnchor221FastPolynomialCell156.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell157.cell.a,MeanAnchor221FastPolynomialCell157.cell.b,MeanAnchor221FastPolynomialCell157.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell158.cell.a,MeanAnchor221FastPolynomialCell158.cell.b,MeanAnchor221FastPolynomialCell158.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell159.cell.a,MeanAnchor221FastPolynomialCell159.cell.b,MeanAnchor221FastPolynomialCell159.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell160.cell.a,MeanAnchor221FastPolynomialCell160.cell.b,MeanAnchor221FastPolynomialCell160.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell161.cell.a,MeanAnchor221FastPolynomialCell161.cell.b,MeanAnchor221FastPolynomialCell161.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell162.cell.a,MeanAnchor221FastPolynomialCell162.cell.b,MeanAnchor221FastPolynomialCell162.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell163.cell.a,MeanAnchor221FastPolynomialCell163.cell.b,MeanAnchor221FastPolynomialCell163.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell164.cell.a,MeanAnchor221FastPolynomialCell164.cell.b,MeanAnchor221FastPolynomialCell164.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell165.cell.a,MeanAnchor221FastPolynomialCell165.cell.b,MeanAnchor221FastPolynomialCell165.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell166.cell.a,MeanAnchor221FastPolynomialCell166.cell.b,MeanAnchor221FastPolynomialCell166.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell167.cell.a,MeanAnchor221FastPolynomialCell167.cell.b,MeanAnchor221FastPolynomialCell167.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell168.cell.a,MeanAnchor221FastPolynomialCell168.cell.b,MeanAnchor221FastPolynomialCell168.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell169.cell.a,MeanAnchor221FastPolynomialCell169.cell.b,MeanAnchor221FastPolynomialCell169.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell170.cell.a,MeanAnchor221FastPolynomialCell170.cell.b,MeanAnchor221FastPolynomialCell170.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell171.cell.a,MeanAnchor221FastPolynomialCell171.cell.b,MeanAnchor221FastPolynomialCell171.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell172.cell.a,MeanAnchor221FastPolynomialCell172.cell.b,MeanAnchor221FastPolynomialCell172.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell173.cell.a,MeanAnchor221FastPolynomialCell173.cell.b,MeanAnchor221FastPolynomialCell173.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell174.cell.a,MeanAnchor221FastPolynomialCell174.cell.b,MeanAnchor221FastPolynomialCell174.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell175.cell.a,MeanAnchor221FastPolynomialCell175.cell.b,MeanAnchor221FastPolynomialCell175.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell176.cell.a,MeanAnchor221FastPolynomialCell176.cell.b,MeanAnchor221FastPolynomialCell176.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell177.cell.a,MeanAnchor221FastPolynomialCell177.cell.b,MeanAnchor221FastPolynomialCell177.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell178.cell.a,MeanAnchor221FastPolynomialCell178.cell.b,MeanAnchor221FastPolynomialCell178.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell179.cell.a,MeanAnchor221FastPolynomialCell179.cell.b,MeanAnchor221FastPolynomialCell179.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell180.cell.a,MeanAnchor221FastPolynomialCell180.cell.b,MeanAnchor221FastPolynomialCell180.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell181.cell.a,MeanAnchor221FastPolynomialCell181.cell.b,MeanAnchor221FastPolynomialCell181.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell182.cell.a,MeanAnchor221FastPolynomialCell182.cell.b,MeanAnchor221FastPolynomialCell182.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell183.cell.a,MeanAnchor221FastPolynomialCell183.cell.b,MeanAnchor221FastPolynomialCell183.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell184.cell.a,MeanAnchor221FastPolynomialCell184.cell.b,MeanAnchor221FastPolynomialCell184.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell185.cell.a,MeanAnchor221FastPolynomialCell185.cell.b,MeanAnchor221FastPolynomialCell185.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell186.cell.a,MeanAnchor221FastPolynomialCell186.cell.b,MeanAnchor221FastPolynomialCell186.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell187.cell.a,MeanAnchor221FastPolynomialCell187.cell.b,MeanAnchor221FastPolynomialCell187.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell188.cell.a,MeanAnchor221FastPolynomialCell188.cell.b,MeanAnchor221FastPolynomialCell188.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell189.cell.a,MeanAnchor221FastPolynomialCell189.cell.b,MeanAnchor221FastPolynomialCell189.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell190.cell.a,MeanAnchor221FastPolynomialCell190.cell.b,MeanAnchor221FastPolynomialCell190.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell191.cell.a,MeanAnchor221FastPolynomialCell191.cell.b,MeanAnchor221FastPolynomialCell191.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell192.cell.a,MeanAnchor221FastPolynomialCell192.cell.b,MeanAnchor221FastPolynomialCell192.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell193.cell.a,MeanAnchor221FastPolynomialCell193.cell.b,MeanAnchor221FastPolynomialCell193.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell194.cell.a,MeanAnchor221FastPolynomialCell194.cell.b,MeanAnchor221FastPolynomialCell194.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell195.cell.a,MeanAnchor221FastPolynomialCell195.cell.b,MeanAnchor221FastPolynomialCell195.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell196.cell.a,MeanAnchor221FastPolynomialCell196.cell.b,MeanAnchor221FastPolynomialCell196.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell197.cell.a,MeanAnchor221FastPolynomialCell197.cell.b,MeanAnchor221FastPolynomialCell197.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell198.cell.a,MeanAnchor221FastPolynomialCell198.cell.b,MeanAnchor221FastPolynomialCell198.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell199.cell.a,MeanAnchor221FastPolynomialCell199.cell.b,MeanAnchor221FastPolynomialCell199.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell200.cell.a,MeanAnchor221FastPolynomialCell200.cell.b,MeanAnchor221FastPolynomialCell200.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell201.cell.a,MeanAnchor221FastPolynomialCell201.cell.b,MeanAnchor221FastPolynomialCell201.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell202.cell.a,MeanAnchor221FastPolynomialCell202.cell.b,MeanAnchor221FastPolynomialCell202.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell203.cell.a,MeanAnchor221FastPolynomialCell203.cell.b,MeanAnchor221FastPolynomialCell203.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell204.cell.a,MeanAnchor221FastPolynomialCell204.cell.b,MeanAnchor221FastPolynomialCell204.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell205.cell.a,MeanAnchor221FastPolynomialCell205.cell.b,MeanAnchor221FastPolynomialCell205.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell206.cell.a,MeanAnchor221FastPolynomialCell206.cell.b,MeanAnchor221FastPolynomialCell206.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell207.cell.a,MeanAnchor221FastPolynomialCell207.cell.b,MeanAnchor221FastPolynomialCell207.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell208.cell.a,MeanAnchor221FastPolynomialCell208.cell.b,MeanAnchor221FastPolynomialCell208.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell209.cell.a,MeanAnchor221FastPolynomialCell209.cell.b,MeanAnchor221FastPolynomialCell209.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell210.cell.a,MeanAnchor221FastPolynomialCell210.cell.b,MeanAnchor221FastPolynomialCell210.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell211.cell.a,MeanAnchor221FastPolynomialCell211.cell.b,MeanAnchor221FastPolynomialCell211.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell212.cell.a,MeanAnchor221FastPolynomialCell212.cell.b,MeanAnchor221FastPolynomialCell212.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell213.cell.a,MeanAnchor221FastPolynomialCell213.cell.b,MeanAnchor221FastPolynomialCell213.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell214.cell.a,MeanAnchor221FastPolynomialCell214.cell.b,MeanAnchor221FastPolynomialCell214.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell215.cell.a,MeanAnchor221FastPolynomialCell215.cell.b,MeanAnchor221FastPolynomialCell215.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell216.cell.a,MeanAnchor221FastPolynomialCell216.cell.b,MeanAnchor221FastPolynomialCell216.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell217.cell.a,MeanAnchor221FastPolynomialCell217.cell.b,MeanAnchor221FastPolynomialCell217.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell218.cell.a,MeanAnchor221FastPolynomialCell218.cell.b,MeanAnchor221FastPolynomialCell218.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell219.cell.a,MeanAnchor221FastPolynomialCell219.cell.b,MeanAnchor221FastPolynomialCell219.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell220.cell.a,MeanAnchor221FastPolynomialCell220.cell.b,MeanAnchor221FastPolynomialCell220.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell221.cell.a,MeanAnchor221FastPolynomialCell221.cell.b,MeanAnchor221FastPolynomialCell221.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell222.cell.a,MeanAnchor221FastPolynomialCell222.cell.b,MeanAnchor221FastPolynomialCell222.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell223.cell.a,MeanAnchor221FastPolynomialCell223.cell.b,MeanAnchor221FastPolynomialCell223.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell224.cell.a,MeanAnchor221FastPolynomialCell224.cell.b,MeanAnchor221FastPolynomialCell224.cell.total⟩,
  ⟨MeanAnchor221FastPolynomialCell225.cell.a,MeanAnchor221FastPolynomialCell225.cell.b,MeanAnchor221FastPolynomialCell225.cell.total⟩
]
def payment : ℚ := (94265607211809/1000000000000000)

theorem chain_checked : check (1/16777216) 128 slices = true := by decide +kernel
theorem total_checked : total slices = payment := by decide +kernel

theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) :
    (payment : ℝ) ≤ ∫ y : ℝ in (1/16777216 : ℝ)..128,
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 0)
        (CoreQuotient.fused G u 0 0) (44/23) y := by
  let f := MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 0) (CoreQuotient.fused G u 0 0) (44/23)
  have hf := ActualFusionIntegral.logarithm_integrable G u 0 0 (44/23)
  have hp : ∀ c ∈ slices, (c.payment : ℝ) ≤ ∫ y : ℝ in (c.a : ℝ)..(c.b : ℝ), f y := by
    intro c hc
    simp only [slices,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact MeanAnchor221FastPolynomialCell000.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell001.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell002.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell003.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell004.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell005.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell006.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell007.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell008.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell009.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell010.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell011.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell012.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell013.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell014.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell015.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell016.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell017.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell018.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell019.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell020.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell021.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell022.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell023.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell024.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell025.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell026.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell027.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell028.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell029.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell030.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell031.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell032.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell033.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell034.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell035.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell036.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell037.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell038.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell039.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell040.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell041.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell042.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell043.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell044.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell045.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell046.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell047.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell048.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell049.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell050.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell051.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell052.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell053.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell054.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell055.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell056.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell057.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell058.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell059.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell060.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell061.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell062.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell063.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell064.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell065.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell066.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell067.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell068.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell069.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell070.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell071.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell072.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell073.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell074.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell075.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell076.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell077.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell078.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell079.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell080.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell081.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell082.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell083.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell084.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell085.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell086.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell087.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell088.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell089.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell090.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell091.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell092.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell093.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell094.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell095.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell096.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell097.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell098.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell099.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell100.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell101.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell102.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell103.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell104.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell105.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell106.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell107.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell108.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell109.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell110.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell111.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell112.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell113.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell114.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell115.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell116.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell117.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell118.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell119.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell120.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell121.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell122.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell123.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell124.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell125.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell126.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell127.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell128.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell129.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell130.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell131.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell132.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell133.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell134.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell135.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell136.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell137.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell138.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell139.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell140.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell141.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell142.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell143.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell144.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell145.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell146.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell147.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell148.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell149.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell150.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell151.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell152.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell153.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell154.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell155.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell156.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell157.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell158.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell159.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell160.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell161.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell162.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell163.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell164.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell165.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell166.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell167.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell168.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell169.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell170.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell171.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell172.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell173.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell174.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell175.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell176.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell177.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell178.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell179.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell180.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell181.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell182.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell183.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell184.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell185.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell186.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell187.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell188.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell189.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell190.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell191.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell192.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell193.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell194.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell195.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell196.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell197.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell198.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell199.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell200.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell201.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell202.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell203.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell204.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell205.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell206.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell207.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell208.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell209.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell210.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell211.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell212.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell213.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell214.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell215.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell216.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell217.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell218.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell219.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell220.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell221.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell222.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell223.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell224.actual_integral G u hd
    · exact MeanAnchor221FastPolynomialCell225.actual_integral G u hd
  have h := RationalIntegralPartition.integral_lower f hf (1/16777216) 128 slices
    (by norm_num) chain_checked hp
  rw [total_checked] at h
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h

#print axioms chain_checked
#print axioms total_checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.MeanAnchor221FinitePayment
