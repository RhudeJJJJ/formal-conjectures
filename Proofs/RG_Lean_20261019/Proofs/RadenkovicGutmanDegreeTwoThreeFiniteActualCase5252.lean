/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5252 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap5252 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5252 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5252_checked : acceptsGraphIso
    (source (graph core5252) (root 7) 2 5) DegreeTwoThreeSpectrum6567.graph sourceMap5252=true := by decide +kernel
theorem fusedMap5252_checked : acceptsGraphIso
    (fused (graph core5252) (root 7) 2 5) DegreeTwoThreeSpectrum5010.graph fusedMap5252=true := by decide +kernel
theorem certified5252 : Certified (graph core5252) (root 7) 2 5 :=
  of_native_maps core5252 DegreeTwoThreeSpectrum6567.graph DegreeTwoThreeSpectrum5010.graph
    sourceMap5252 fusedMap5252 sourceMap5252_checked fusedMap5252_checked
    DegreeTwoThreeFiniteComparisons.comparison5252
#print axioms sourceMap5252_checked
#print axioms fusedMap5252_checked
#print axioms certified5252
def sourceMap5252swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5252swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5252swap_checked : acceptsGraphIso
    (source (graph core5252) (root 7) 5 2) DegreeTwoThreeSpectrum6567.graph sourceMap5252swap=true := by decide +kernel
theorem fusedMap5252swap_checked : acceptsGraphIso
    (fused (graph core5252) (root 7) 5 2) DegreeTwoThreeSpectrum5010.graph fusedMap5252swap=true := by decide +kernel
theorem certified5252swap : Certified (graph core5252) (root 7) 5 2 :=
  of_native_maps core5252 DegreeTwoThreeSpectrum6567.graph DegreeTwoThreeSpectrum5010.graph
    sourceMap5252swap fusedMap5252swap sourceMap5252swap_checked fusedMap5252swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5252
#print axioms sourceMap5252swap_checked
#print axioms fusedMap5252swap_checked
#print axioms certified5252swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
