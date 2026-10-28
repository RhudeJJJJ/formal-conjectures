/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5403 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5403 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5,11,12,13,14,15,16] (sourceLabel 5 4 5 v)
def fusedMap5403 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 5 4 5 v)
theorem sourceMap5403_checked : acceptsGraphIso
    (source (graph core5403) (root 5) 4 5) DegreeTwoThreeSpectrum5913.graph sourceMap5403=true := by decide +kernel
theorem fusedMap5403_checked : acceptsGraphIso
    (fused (graph core5403) (root 5) 4 5) DegreeTwoThreeSpectrum4962.graph fusedMap5403=true := by decide +kernel
theorem certified5403 : Certified (graph core5403) (root 5) 4 5 :=
  of_native_maps core5403 DegreeTwoThreeSpectrum5913.graph DegreeTwoThreeSpectrum4962.graph
    sourceMap5403 fusedMap5403 sourceMap5403_checked fusedMap5403_checked
    DegreeTwoThreeFiniteComparisons.comparison5403
#print axioms sourceMap5403_checked
#print axioms fusedMap5403_checked
#print axioms certified5403
def sourceMap5403swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5] (sourceLabel 5 5 4 v)
def fusedMap5403swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 5 5 4 v)
theorem sourceMap5403swap_checked : acceptsGraphIso
    (source (graph core5403) (root 5) 5 4) DegreeTwoThreeSpectrum5913.graph sourceMap5403swap=true := by decide +kernel
theorem fusedMap5403swap_checked : acceptsGraphIso
    (fused (graph core5403) (root 5) 5 4) DegreeTwoThreeSpectrum4962.graph fusedMap5403swap=true := by decide +kernel
theorem certified5403swap : Certified (graph core5403) (root 5) 5 4 :=
  of_native_maps core5403 DegreeTwoThreeSpectrum5913.graph DegreeTwoThreeSpectrum4962.graph
    sourceMap5403swap fusedMap5403swap sourceMap5403swap_checked fusedMap5403swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5403
#print axioms sourceMap5403swap_checked
#print axioms fusedMap5403swap_checked
#print axioms certified5403swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
