/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5412 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5412 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,7,8,9,10,2,3,4,5,6,0,11,12,13,14,15,16] (sourceLabel 4 4 6 v)
def fusedMap5412 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 4 6 v)
theorem sourceMap5412_checked : acceptsGraphIso
    (source (graph core5412) (root 4) 4 6) DegreeTwoThreeSpectrum5933.graph sourceMap5412=true := by decide +kernel
theorem fusedMap5412_checked : acceptsGraphIso
    (fused (graph core5412) (root 4) 4 6) DegreeTwoThreeSpectrum4980.graph fusedMap5412=true := by decide +kernel
theorem certified5412 : Certified (graph core5412) (root 4) 4 6 :=
  of_native_maps core5412 DegreeTwoThreeSpectrum5933.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap5412 fusedMap5412 sourceMap5412_checked fusedMap5412_checked
    DegreeTwoThreeFiniteComparisons.comparison5412
#print axioms sourceMap5412_checked
#print axioms fusedMap5412_checked
#print axioms certified5412
def sourceMap5412swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,7,8,9,10,0,11,12,13,14,15,16,2,3,4,5,6] (sourceLabel 4 6 4 v)
def fusedMap5412swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 6 4 v)
theorem sourceMap5412swap_checked : acceptsGraphIso
    (source (graph core5412) (root 4) 6 4) DegreeTwoThreeSpectrum5933.graph sourceMap5412swap=true := by decide +kernel
theorem fusedMap5412swap_checked : acceptsGraphIso
    (fused (graph core5412) (root 4) 6 4) DegreeTwoThreeSpectrum4980.graph fusedMap5412swap=true := by decide +kernel
theorem certified5412swap : Certified (graph core5412) (root 4) 6 4 :=
  of_native_maps core5412 DegreeTwoThreeSpectrum5933.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap5412swap fusedMap5412swap sourceMap5412swap_checked fusedMap5412swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5412
#print axioms sourceMap5412swap_checked
#print axioms fusedMap5412swap_checked
#print axioms certified5412swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
