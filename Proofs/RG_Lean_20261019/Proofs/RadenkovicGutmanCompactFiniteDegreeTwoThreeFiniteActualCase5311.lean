/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5311 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5311 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,7,8,9,1,0,11,12,13,14,15,16] (sourceLabel 5 2 7 v)
def fusedMap5311 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 5 2 7 v)
theorem sourceMap5311_checked : acceptsGraphIso
    (source (graph core5311) (root 5) 2 7) DegreeTwoThreeSpectrum5833.graph sourceMap5311=true := by decide +kernel
theorem fusedMap5311_checked : acceptsGraphIso
    (fused (graph core5311) (root 5) 2 7) DegreeTwoThreeSpectrum4962.graph fusedMap5311=true := by decide +kernel
theorem certified5311 : Certified (graph core5311) (root 5) 2 7 :=
  of_native_maps core5311 DegreeTwoThreeSpectrum5833.graph DegreeTwoThreeSpectrum4962.graph
    sourceMap5311 fusedMap5311 sourceMap5311_checked fusedMap5311_checked
    DegreeTwoThreeFiniteComparisons.comparison5311
#print axioms sourceMap5311_checked
#print axioms fusedMap5311_checked
#print axioms certified5311
def sourceMap5311swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,1,0,11,12,13,14,15,16,7,8,9] (sourceLabel 5 7 2 v)
def fusedMap5311swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 5 7 2 v)
theorem sourceMap5311swap_checked : acceptsGraphIso
    (source (graph core5311) (root 5) 7 2) DegreeTwoThreeSpectrum5833.graph sourceMap5311swap=true := by decide +kernel
theorem fusedMap5311swap_checked : acceptsGraphIso
    (fused (graph core5311) (root 5) 7 2) DegreeTwoThreeSpectrum4962.graph fusedMap5311swap=true := by decide +kernel
theorem certified5311swap : Certified (graph core5311) (root 5) 7 2 :=
  of_native_maps core5311 DegreeTwoThreeSpectrum5833.graph DegreeTwoThreeSpectrum4962.graph
    sourceMap5311swap fusedMap5311swap sourceMap5311swap_checked fusedMap5311swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5311
#print axioms sourceMap5311swap_checked
#print axioms fusedMap5311swap_checked
#print axioms certified5311swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
