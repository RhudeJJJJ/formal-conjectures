/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2082 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap2082 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,6,7,1,2,3,4,5] (sourceLabel 7 0 4 v)
def fusedMap2082 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (fusedLabel 7 0 4 v)
theorem sourceMap2082_checked : acceptsGraphIso
    (source (graph core2082) (root 7) 0 4) DegreeTwoThreeSpectrum1736.graph sourceMap2082=true := by decide +kernel
theorem fusedMap2082_checked : acceptsGraphIso
    (fused (graph core2082) (root 7) 0 4) DegreeTwoThreeSpectrum1738.graph fusedMap2082=true := by decide +kernel
theorem certified2082 : Certified (graph core2082) (root 7) 0 4 :=
  of_native_maps core2082 DegreeTwoThreeSpectrum1736.graph DegreeTwoThreeSpectrum1738.graph
    sourceMap2082 fusedMap2082 sourceMap2082_checked fusedMap2082_checked
    DegreeTwoThreeFiniteComparisons.comparison2082
#print axioms sourceMap2082_checked
#print axioms fusedMap2082_checked
#print axioms certified2082
def sourceMap2082swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,6,1,2,3,4,5,7] (sourceLabel 7 4 0 v)
def fusedMap2082swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (fusedLabel 7 4 0 v)
theorem sourceMap2082swap_checked : acceptsGraphIso
    (source (graph core2082) (root 7) 4 0) DegreeTwoThreeSpectrum1736.graph sourceMap2082swap=true := by decide +kernel
theorem fusedMap2082swap_checked : acceptsGraphIso
    (fused (graph core2082) (root 7) 4 0) DegreeTwoThreeSpectrum1738.graph fusedMap2082swap=true := by decide +kernel
theorem certified2082swap : Certified (graph core2082) (root 7) 4 0 :=
  of_native_maps core2082 DegreeTwoThreeSpectrum1736.graph DegreeTwoThreeSpectrum1738.graph
    sourceMap2082swap fusedMap2082swap sourceMap2082swap_checked fusedMap2082swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2082
#print axioms sourceMap2082swap_checked
#print axioms fusedMap2082swap_checked
#print axioms certified2082swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
