/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5305 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap5305 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,11,3,4,5,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5305 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5305_checked : acceptsGraphIso
    (source (graph core5305) (root 6) 2 6) DegreeTwoThreeSpectrum6880.graph sourceMap5305=true := by decide +kernel
theorem fusedMap5305_checked : acceptsGraphIso
    (fused (graph core5305) (root 6) 2 6) DegreeTwoThreeSpectrum5228.graph fusedMap5305=true := by decide +kernel
theorem certified5305 : Certified (graph core5305) (root 6) 2 6 :=
  of_native_maps core5305 DegreeTwoThreeSpectrum6880.graph DegreeTwoThreeSpectrum5228.graph
    sourceMap5305 fusedMap5305 sourceMap5305_checked fusedMap5305_checked
    DegreeTwoThreeFiniteComparisons.comparison5305
#print axioms sourceMap5305_checked
#print axioms fusedMap5305_checked
#print axioms certified5305
def sourceMap5305swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,11,1,0,12,13,14,15,16,3,4,5] (sourceLabel 6 6 2 v)
def fusedMap5305swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5305swap_checked : acceptsGraphIso
    (source (graph core5305) (root 6) 6 2) DegreeTwoThreeSpectrum6880.graph sourceMap5305swap=true := by decide +kernel
theorem fusedMap5305swap_checked : acceptsGraphIso
    (fused (graph core5305) (root 6) 6 2) DegreeTwoThreeSpectrum5228.graph fusedMap5305swap=true := by decide +kernel
theorem certified5305swap : Certified (graph core5305) (root 6) 6 2 :=
  of_native_maps core5305 DegreeTwoThreeSpectrum6880.graph DegreeTwoThreeSpectrum5228.graph
    sourceMap5305swap fusedMap5305swap sourceMap5305swap_checked fusedMap5305swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5305
#print axioms sourceMap5305swap_checked
#print axioms fusedMap5305swap_checked
#print axioms certified5305swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
