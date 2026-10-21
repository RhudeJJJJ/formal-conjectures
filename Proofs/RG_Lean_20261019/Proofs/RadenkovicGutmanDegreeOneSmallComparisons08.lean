/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum043
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum044
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum053
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum069
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum070
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum071
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum073
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum080
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1022
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1096
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum110
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1101
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum111
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1119
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1124
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum114
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum115
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1302
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1306
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum132
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum133
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1354
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1358
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1536
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum165
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1666
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum168
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum176
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum177
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1770
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1807
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1911
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1942
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1976
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum198
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum278
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum281
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum288
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum291
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum322
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum324
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum430
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum434
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum436
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum440
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum502
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum505
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum707
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum727
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum786
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum863
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum871
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum872
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum909
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum916
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum980
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum985
import Proofs.RadenkovicGutmanSmallGeFourSpectrum007
import Proofs.RadenkovicGutmanSmallGeFourSpectrum009
import Proofs.RadenkovicGutmanSmallGeFourSpectrum010
import Proofs.RadenkovicGutmanSmallGeFourSpectrum011
import Proofs.RadenkovicGutmanSmallGeFourSpectrum015
import Proofs.RadenkovicGutmanSmallGeFourSpectrum021
import Proofs.RadenkovicGutmanSmallGeFourSpectrum022
import Proofs.RadenkovicGutmanSmallGeFourSpectrum029
import Proofs.RadenkovicGutmanSmallGeFourSpectrum038
import Proofs.RadenkovicGutmanSmallGeFourSpectrum041
import Proofs.RadenkovicGutmanSmallGeFourSpectrum044
import Proofs.RadenkovicGutmanSmallGeFourSpectrum059
import Proofs.RadenkovicGutmanSmallGeFourSpectrum065
import Proofs.RadenkovicGutmanSmallGeFourSpectrum078
import Proofs.RadenkovicGutmanSmallGeFourSpectrum093
import Proofs.RadenkovicGutmanSmallGeFourSpectrum101
import Proofs.RadenkovicGutmanSmallGeFourSpectrum104
import Proofs.RadenkovicGutmanSmallGeFourSpectrum117
import Proofs.RadenkovicGutmanSmallGeFourSpectrum121
import Proofs.RadenkovicGutmanSmallGeFourSpectrum187
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0400 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1022.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1022.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison0400
theorem comparison0401 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1666.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1666.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison0401
theorem comparison0402 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum043.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum069.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum069.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum043.actual_graph_bounds.2
  linarith
#print axioms comparison0402
theorem comparison0403 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum111.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum110.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum110.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum111.actual_graph_bounds.2
  linarith
#print axioms comparison0403
theorem comparison0404 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum176.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum281.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum281.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum176.actual_graph_bounds.2
  linarith
#print axioms comparison0404
theorem comparison0405 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum434.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum430.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum430.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum434.actual_graph_bounds.2
  linarith
#print axioms comparison0405
theorem comparison0406 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1101.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1101.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum871.actual_graph_bounds.2
  linarith
#print axioms comparison0406
theorem comparison0407 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum176.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum278.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum278.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum176.actual_graph_bounds.2
  linarith
#print axioms comparison0407
theorem comparison0408 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum434.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum707.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum707.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum434.actual_graph_bounds.2
  linarith
#print axioms comparison0408
theorem comparison0409 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1096.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1096.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum871.actual_graph_bounds.2
  linarith
#print axioms comparison0409
theorem comparison0410 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1770.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1770.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum871.actual_graph_bounds.2
  linarith
#print axioms comparison0410
theorem comparison0411 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum044.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum070.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum070.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum044.actual_graph_bounds.2
  linarith
#print axioms comparison0411
theorem comparison0412 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum115.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum114.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum114.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum115.actual_graph_bounds.2
  linarith
#print axioms comparison0412
theorem comparison0413 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum177.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum291.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum291.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum177.actual_graph_bounds.2
  linarith
#print axioms comparison0413
theorem comparison0414 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum440.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum436.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum436.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum440.actual_graph_bounds.2
  linarith
#print axioms comparison0414
theorem comparison0415 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1124.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1124.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum872.actual_graph_bounds.2
  linarith
#print axioms comparison0415
theorem comparison0416 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum177.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum288.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum288.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum177.actual_graph_bounds.2
  linarith
#print axioms comparison0416
theorem comparison0417 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum440.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum727.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum727.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum440.actual_graph_bounds.2
  linarith
#print axioms comparison0417
theorem comparison0418 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1119.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1119.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum872.actual_graph_bounds.2
  linarith
#print axioms comparison0418
theorem comparison0419 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1807.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1807.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum872.actual_graph_bounds.2
  linarith
#print axioms comparison0419
theorem comparison0420 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum053.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum071.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum071.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum053.actual_graph_bounds.2
  linarith
#print axioms comparison0420
theorem comparison0421 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum133.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum132.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum132.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum133.actual_graph_bounds.2
  linarith
#print axioms comparison0421
theorem comparison0422 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum198.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum324.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum324.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum198.actual_graph_bounds.2
  linarith
#print axioms comparison0422
theorem comparison0423 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum505.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum502.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum502.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum505.actual_graph_bounds.2
  linarith
#print axioms comparison0423
theorem comparison0424 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum909.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1306.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1306.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum909.actual_graph_bounds.2
  linarith
#print axioms comparison0424
theorem comparison0425 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum198.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum322.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum322.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum198.actual_graph_bounds.2
  linarith
#print axioms comparison0425
theorem comparison0426 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum505.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum786.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum786.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum505.actual_graph_bounds.2
  linarith
#print axioms comparison0426
theorem comparison0427 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum909.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1302.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1302.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum909.actual_graph_bounds.2
  linarith
#print axioms comparison0427
theorem comparison0428 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum909.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1911.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1911.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum909.actual_graph_bounds.2
  linarith
#print axioms comparison0428
theorem comparison0429 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum007.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum011.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum011.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum007.actual_graph_bounds.2
  linarith
#print axioms comparison0429
theorem comparison0430 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum022.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum021.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum021.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum022.actual_graph_bounds.2
  linarith
#print axioms comparison0430
theorem comparison0431 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum065.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum065.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum038.actual_graph_bounds.2
  linarith
#print axioms comparison0431
theorem comparison0432 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum101.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum101.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison0432
theorem comparison0433 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum916.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1358.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1358.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum916.actual_graph_bounds.2
  linarith
#print axioms comparison0433
theorem comparison0434 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum059.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum059.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum038.actual_graph_bounds.2
  linarith
#print axioms comparison0434
theorem comparison0435 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum187.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum187.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison0435
theorem comparison0436 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum916.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1354.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1354.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum916.actual_graph_bounds.2
  linarith
#print axioms comparison0436
theorem comparison0437 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum916.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1942.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1942.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum916.actual_graph_bounds.2
  linarith
#print axioms comparison0437
theorem comparison0438 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum010.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum009.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum009.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison0438
theorem comparison0439 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum015.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum029.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum029.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum015.actual_graph_bounds.2
  linarith
#print axioms comparison0439
theorem comparison0440 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum044.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum041.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum041.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum044.actual_graph_bounds.2
  linarith
#print axioms comparison0440
theorem comparison0441 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum121.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum121.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison0441
theorem comparison0442 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum985.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum980.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum980.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum985.actual_graph_bounds.2
  linarith
#print axioms comparison0442
theorem comparison0443 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum044.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum078.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum078.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum044.actual_graph_bounds.2
  linarith
#print axioms comparison0443
theorem comparison0444 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum117.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum117.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison0444
theorem comparison0445 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum985.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1536.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1536.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum985.actual_graph_bounds.2
  linarith
#print axioms comparison0445
theorem comparison0446 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum985.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1976.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1976.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum985.actual_graph_bounds.2
  linarith
#print axioms comparison0446
theorem comparison0447 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum080.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0447
theorem comparison0448 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum165.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0448
theorem comparison0449 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum392.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0449
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
