/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5266 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap5266 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5266 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5266_checked : acceptsGraphIso
    (source (graph core5266) (root 7) 2 5) DegreeTwoThreeSpectrum6285.graph sourceMap5266=true := by decide +kernel
theorem fusedMap5266_checked : acceptsGraphIso
    (fused (graph core5266) (root 7) 2 5) DegreeTwoThreeSpectrum5269.graph fusedMap5266=true := by decide +kernel
theorem certified5266 : Certified (graph core5266) (root 7) 2 5 :=
  of_native_maps core5266 DegreeTwoThreeSpectrum6285.graph DegreeTwoThreeSpectrum5269.graph
    sourceMap5266 fusedMap5266 sourceMap5266_checked fusedMap5266_checked
    DegreeTwoThreeFiniteComparisons.comparison5266
#print axioms sourceMap5266_checked
#print axioms fusedMap5266_checked
#print axioms certified5266
def sourceMap5266swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5266swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5266swap_checked : acceptsGraphIso
    (source (graph core5266) (root 7) 5 2) DegreeTwoThreeSpectrum6285.graph sourceMap5266swap=true := by decide +kernel
theorem fusedMap5266swap_checked : acceptsGraphIso
    (fused (graph core5266) (root 7) 5 2) DegreeTwoThreeSpectrum5269.graph fusedMap5266swap=true := by decide +kernel
theorem certified5266swap : Certified (graph core5266) (root 7) 5 2 :=
  of_native_maps core5266 DegreeTwoThreeSpectrum6285.graph DegreeTwoThreeSpectrum5269.graph
    sourceMap5266swap fusedMap5266swap sourceMap5266swap_checked fusedMap5266swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5266
#print axioms sourceMap5266swap_checked
#print axioms fusedMap5266swap_checked
#print axioms certified5266swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
