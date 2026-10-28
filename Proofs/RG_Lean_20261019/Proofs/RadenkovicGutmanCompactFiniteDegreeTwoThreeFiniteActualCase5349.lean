/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5349 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap5349 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5349 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5349_checked : acceptsGraphIso
    (source (graph core5349) (root 6) 3 4) DegreeTwoThreeSpectrum4644.graph sourceMap5349=true := by decide +kernel
theorem fusedMap5349_checked : acceptsGraphIso
    (fused (graph core5349) (root 6) 3 4) DegreeTwoThreeSpectrum3893.graph fusedMap5349=true := by decide +kernel
theorem certified5349 : Certified (graph core5349) (root 6) 3 4 :=
  of_native_maps core5349 DegreeTwoThreeSpectrum4644.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap5349 fusedMap5349 sourceMap5349_checked fusedMap5349_checked
    DegreeTwoThreeFiniteComparisons.comparison5349
#print axioms sourceMap5349_checked
#print axioms fusedMap5349_checked
#print axioms certified5349
def sourceMap5349swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5349swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5349swap_checked : acceptsGraphIso
    (source (graph core5349) (root 6) 4 3) DegreeTwoThreeSpectrum4644.graph sourceMap5349swap=true := by decide +kernel
theorem fusedMap5349swap_checked : acceptsGraphIso
    (fused (graph core5349) (root 6) 4 3) DegreeTwoThreeSpectrum3893.graph fusedMap5349swap=true := by decide +kernel
theorem certified5349swap : Certified (graph core5349) (root 6) 4 3 :=
  of_native_maps core5349 DegreeTwoThreeSpectrum4644.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap5349swap fusedMap5349swap sourceMap5349swap_checked fusedMap5349swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5349
#print axioms sourceMap5349swap_checked
#print axioms fusedMap5349swap_checked
#print axioms certified5349swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
