/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5293 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap5293 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5293 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5293_checked : acceptsGraphIso
    (source (graph core5293) (root 6) 2 6) DegreeTwoThreeSpectrum5763.graph sourceMap5293=true := by decide +kernel
theorem fusedMap5293_checked : acceptsGraphIso
    (fused (graph core5293) (root 6) 2 6) DegreeTwoThreeSpectrum5066.graph fusedMap5293=true := by decide +kernel
theorem certified5293 : Certified (graph core5293) (root 6) 2 6 :=
  of_native_maps core5293 DegreeTwoThreeSpectrum5763.graph DegreeTwoThreeSpectrum5066.graph
    sourceMap5293 fusedMap5293 sourceMap5293_checked fusedMap5293_checked
    DegreeTwoThreeFiniteComparisons.comparison5293
#print axioms sourceMap5293_checked
#print axioms fusedMap5293_checked
#print axioms certified5293
def sourceMap5293swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,16,7,8,9] (sourceLabel 6 6 2 v)
def fusedMap5293swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5293swap_checked : acceptsGraphIso
    (source (graph core5293) (root 6) 6 2) DegreeTwoThreeSpectrum5763.graph sourceMap5293swap=true := by decide +kernel
theorem fusedMap5293swap_checked : acceptsGraphIso
    (fused (graph core5293) (root 6) 6 2) DegreeTwoThreeSpectrum5066.graph fusedMap5293swap=true := by decide +kernel
theorem certified5293swap : Certified (graph core5293) (root 6) 6 2 :=
  of_native_maps core5293 DegreeTwoThreeSpectrum5763.graph DegreeTwoThreeSpectrum5066.graph
    sourceMap5293swap fusedMap5293swap sourceMap5293swap_checked fusedMap5293swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5293
#print axioms sourceMap5293swap_checked
#print axioms fusedMap5293swap_checked
#print axioms certified5293swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
