/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5180 : Family 8 := level8.get ⟨183,by decide⟩
def sourceMap5180 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5180 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5180_checked : acceptsGraphIso
    (source (graph core5180) (root 8) 2 4) DegreeTwoThreeSpectrum7017.graph sourceMap5180=true := by decide +kernel
theorem fusedMap5180_checked : acceptsGraphIso
    (fused (graph core5180) (root 8) 2 4) DegreeTwoThreeSpectrum5842.graph fusedMap5180=true := by decide +kernel
theorem certified5180 : Certified (graph core5180) (root 8) 2 4 :=
  of_native_maps core5180 DegreeTwoThreeSpectrum7017.graph DegreeTwoThreeSpectrum5842.graph
    sourceMap5180 fusedMap5180 sourceMap5180_checked fusedMap5180_checked
    DegreeTwoThreeFiniteComparisons.comparison5180
#print axioms sourceMap5180_checked
#print axioms fusedMap5180_checked
#print axioms certified5180
def sourceMap5180swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,14,15,16,5,6,7] (sourceLabel 8 4 2 v)
def fusedMap5180swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5180swap_checked : acceptsGraphIso
    (source (graph core5180) (root 8) 4 2) DegreeTwoThreeSpectrum7017.graph sourceMap5180swap=true := by decide +kernel
theorem fusedMap5180swap_checked : acceptsGraphIso
    (fused (graph core5180) (root 8) 4 2) DegreeTwoThreeSpectrum5842.graph fusedMap5180swap=true := by decide +kernel
theorem certified5180swap : Certified (graph core5180) (root 8) 4 2 :=
  of_native_maps core5180 DegreeTwoThreeSpectrum7017.graph DegreeTwoThreeSpectrum5842.graph
    sourceMap5180swap fusedMap5180swap sourceMap5180swap_checked fusedMap5180swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5180
#print axioms sourceMap5180swap_checked
#print axioms fusedMap5180swap_checked
#print axioms certified5180swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
