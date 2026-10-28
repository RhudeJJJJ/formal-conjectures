/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5290 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap5290 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5290 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5290_checked : acceptsGraphIso
    (source (graph core5290) (root 6) 2 6) DegreeTwoThreeSpectrum5925.graph sourceMap5290=true := by decide +kernel
theorem fusedMap5290_checked : acceptsGraphIso
    (fused (graph core5290) (root 6) 2 6) DegreeTwoThreeSpectrum4963.graph fusedMap5290=true := by decide +kernel
theorem certified5290 : Certified (graph core5290) (root 6) 2 6 :=
  of_native_maps core5290 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum4963.graph
    sourceMap5290 fusedMap5290 sourceMap5290_checked fusedMap5290_checked
    DegreeTwoThreeFiniteComparisons.comparison5290
#print axioms sourceMap5290_checked
#print axioms fusedMap5290_checked
#print axioms certified5290
def sourceMap5290swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,16,7,8,9] (sourceLabel 6 6 2 v)
def fusedMap5290swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5290swap_checked : acceptsGraphIso
    (source (graph core5290) (root 6) 6 2) DegreeTwoThreeSpectrum5925.graph sourceMap5290swap=true := by decide +kernel
theorem fusedMap5290swap_checked : acceptsGraphIso
    (fused (graph core5290) (root 6) 6 2) DegreeTwoThreeSpectrum4963.graph fusedMap5290swap=true := by decide +kernel
theorem certified5290swap : Certified (graph core5290) (root 6) 6 2 :=
  of_native_maps core5290 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum4963.graph
    sourceMap5290swap fusedMap5290swap sourceMap5290swap_checked fusedMap5290swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5290
#print axioms sourceMap5290swap_checked
#print axioms fusedMap5290swap_checked
#print axioms certified5290swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
