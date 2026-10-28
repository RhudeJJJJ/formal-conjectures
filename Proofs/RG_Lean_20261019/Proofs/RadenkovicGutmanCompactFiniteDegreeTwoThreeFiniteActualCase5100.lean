/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5100 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap5100 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5100 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5100_checked : acceptsGraphIso
    (source (graph core5100) (root 7) 2 4) DegreeTwoThreeSpectrum4641.graph sourceMap5100=true := by decide +kernel
theorem fusedMap5100_checked : acceptsGraphIso
    (fused (graph core5100) (root 7) 2 4) DegreeTwoThreeSpectrum4124.graph fusedMap5100=true := by decide +kernel
theorem certified5100 : Certified (graph core5100) (root 7) 2 4 :=
  of_native_maps core5100 DegreeTwoThreeSpectrum4641.graph DegreeTwoThreeSpectrum4124.graph
    sourceMap5100 fusedMap5100 sourceMap5100_checked fusedMap5100_checked
    DegreeTwoThreeFiniteComparisons.comparison5100
#print axioms sourceMap5100_checked
#print axioms fusedMap5100_checked
#print axioms certified5100
def sourceMap5100swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,14,15,5,6,7] (sourceLabel 7 4 2 v)
def fusedMap5100swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5100swap_checked : acceptsGraphIso
    (source (graph core5100) (root 7) 4 2) DegreeTwoThreeSpectrum4641.graph sourceMap5100swap=true := by decide +kernel
theorem fusedMap5100swap_checked : acceptsGraphIso
    (fused (graph core5100) (root 7) 4 2) DegreeTwoThreeSpectrum4124.graph fusedMap5100swap=true := by decide +kernel
theorem certified5100swap : Certified (graph core5100) (root 7) 4 2 :=
  of_native_maps core5100 DegreeTwoThreeSpectrum4641.graph DegreeTwoThreeSpectrum4124.graph
    sourceMap5100swap fusedMap5100swap sourceMap5100swap_checked fusedMap5100swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5100
#print axioms sourceMap5100swap_checked
#print axioms fusedMap5100swap_checked
#print axioms certified5100swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
