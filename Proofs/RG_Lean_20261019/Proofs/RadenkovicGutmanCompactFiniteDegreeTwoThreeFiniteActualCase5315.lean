/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5315 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5315 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,3,4,5,1,0,11,12,13,14,15,16] (sourceLabel 5 2 7 v)
def fusedMap5315 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 2 7 v)
theorem sourceMap5315_checked : acceptsGraphIso
    (source (graph core5315) (root 5) 2 7) DegreeTwoThreeSpectrum5672.graph sourceMap5315=true := by decide +kernel
theorem fusedMap5315_checked : acceptsGraphIso
    (fused (graph core5315) (root 5) 2 7) DegreeTwoThreeSpectrum4966.graph fusedMap5315=true := by decide +kernel
theorem certified5315 : Certified (graph core5315) (root 5) 2 7 :=
  of_native_maps core5315 DegreeTwoThreeSpectrum5672.graph DegreeTwoThreeSpectrum4966.graph
    sourceMap5315 fusedMap5315 sourceMap5315_checked fusedMap5315_checked
    DegreeTwoThreeFiniteComparisons.comparison5315
#print axioms sourceMap5315_checked
#print axioms fusedMap5315_checked
#print axioms certified5315
def sourceMap5315swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,1,0,11,12,13,14,15,16,3,4,5] (sourceLabel 5 7 2 v)
def fusedMap5315swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 7 2 v)
theorem sourceMap5315swap_checked : acceptsGraphIso
    (source (graph core5315) (root 5) 7 2) DegreeTwoThreeSpectrum5672.graph sourceMap5315swap=true := by decide +kernel
theorem fusedMap5315swap_checked : acceptsGraphIso
    (fused (graph core5315) (root 5) 7 2) DegreeTwoThreeSpectrum4966.graph fusedMap5315swap=true := by decide +kernel
theorem certified5315swap : Certified (graph core5315) (root 5) 7 2 :=
  of_native_maps core5315 DegreeTwoThreeSpectrum5672.graph DegreeTwoThreeSpectrum4966.graph
    sourceMap5315swap fusedMap5315swap sourceMap5315swap_checked fusedMap5315swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5315
#print axioms sourceMap5315swap_checked
#print axioms fusedMap5315swap_checked
#print axioms certified5315swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
