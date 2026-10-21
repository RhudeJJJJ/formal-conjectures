/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum074
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum075
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum076
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum077
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum078
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum079
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum080
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum086
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum090
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum091
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum103
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1077
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum117
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1177
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum122
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum164
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum165
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum167
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum173
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum175
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum180
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum182
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum186
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum188
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum193
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum212
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum213
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum216
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum217
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum371
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum372
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum376
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum378
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum379
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum384
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum386
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum389
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum390
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum391
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum397
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum421
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum426
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum450
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum456
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum472
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum478
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum483
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum510
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum514
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum517
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum518
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum859
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum860
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum861
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum869
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum878
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum879
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum886
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum887
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum901
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum907
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum937
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum943
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum948
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum949
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum950
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum951
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum965
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum975
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum976
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0450 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum859.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0450
theorem comparison0451 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum379.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0451
theorem comparison0452 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum951.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0452
theorem comparison0453 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum077.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum077.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0453
theorem comparison0454 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum193.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum193.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0454
theorem comparison0455 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum376.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum376.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0455
theorem comparison0456 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum907.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum907.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0456
theorem comparison0457 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum483.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum483.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0457
theorem comparison0458 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum901.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum901.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0458
theorem comparison0459 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum078.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum078.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum086.actual_graph_bounds.2
  linarith
#print axioms comparison0459
theorem comparison0460 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum213.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum213.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0460
theorem comparison0461 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum384.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum384.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0461
theorem comparison0462 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum943.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum943.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0462
theorem comparison0463 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum514.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum514.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0463
theorem comparison0464 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum937.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum937.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0464
theorem comparison0465 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum079.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum079.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum090.actual_graph_bounds.2
  linarith
#print axioms comparison0465
theorem comparison0466 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum216.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum216.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison0466
theorem comparison0467 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum390.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum390.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0467
theorem comparison0468 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum965.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum965.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0468
theorem comparison0469 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum517.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum517.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0469
theorem comparison0470 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum949.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum949.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0470
theorem comparison0471 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum091.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum076.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum076.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum091.actual_graph_bounds.2
  linarith
#print axioms comparison0471
theorem comparison0472 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum217.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum217.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison0472
theorem comparison0473 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum391.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum391.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison0473
theorem comparison0474 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum975.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum975.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison0474
theorem comparison0475 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum518.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum518.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison0475
theorem comparison0476 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum950.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum950.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison0476
theorem comparison0477 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum075.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum075.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum090.actual_graph_bounds.2
  linarith
#print axioms comparison0477
theorem comparison0478 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum212.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum212.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison0478
theorem comparison0479 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum397.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum389.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum389.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum397.actual_graph_bounds.2
  linarith
#print axioms comparison0479
theorem comparison0480 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum976.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum976.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison0480
theorem comparison0481 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum397.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum510.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum510.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum397.actual_graph_bounds.2
  linarith
#print axioms comparison0481
theorem comparison0482 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum948.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum948.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison0482
theorem comparison0483 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum103.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum103.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison0483
theorem comparison0484 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum173.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum173.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0484
theorem comparison0485 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum426.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum426.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0485
theorem comparison0486 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum869.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum869.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0486
theorem comparison0487 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum421.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum421.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0487
theorem comparison0488 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1077.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1077.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0488
theorem comparison0489 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum075.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum117.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum117.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum075.actual_graph_bounds.2
  linarith
#print axioms comparison0489
theorem comparison0490 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum180.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum180.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum182.actual_graph_bounds.2
  linarith
#print axioms comparison0490
theorem comparison0491 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum456.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum456.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0491
theorem comparison0492 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum878.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum878.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0492
theorem comparison0493 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum450.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum450.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0493
theorem comparison0494 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1177.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1177.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0494
theorem comparison0495 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum076.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum122.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum122.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum076.actual_graph_bounds.2
  linarith
#print axioms comparison0495
theorem comparison0496 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum188.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum186.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum186.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum188.actual_graph_bounds.2
  linarith
#print axioms comparison0496
theorem comparison0497 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum478.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum478.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum372.actual_graph_bounds.2
  linarith
#print axioms comparison0497
theorem comparison0498 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum886.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum886.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison0498
theorem comparison0499 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum472.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum472.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum372.actual_graph_bounds.2
  linarith
#print axioms comparison0499
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
