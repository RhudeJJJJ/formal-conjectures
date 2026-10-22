/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5147 : Family 8 := level8.get ⟨105,by decide⟩
def sourceMap5147 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5147 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5147_checked : acceptsGraphIso
    (source (graph core5147) (root 8) 2 4) DegreeTwoThreeSpectrum6144.graph sourceMap5147=true := by decide +kernel
theorem fusedMap5147_checked : acceptsGraphIso
    (fused (graph core5147) (root 8) 2 4) DegreeTwoThreeSpectrum5195.graph fusedMap5147=true := by decide +kernel
theorem certified5147 : Certified (graph core5147) (root 8) 2 4 :=
  of_native_maps core5147 DegreeTwoThreeSpectrum6144.graph DegreeTwoThreeSpectrum5195.graph
    sourceMap5147 fusedMap5147 sourceMap5147_checked fusedMap5147_checked
    DegreeTwoThreeFiniteComparisons.comparison5147
#print axioms sourceMap5147_checked
#print axioms fusedMap5147_checked
#print axioms certified5147
def sourceMap5147swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5147swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5147swap_checked : acceptsGraphIso
    (source (graph core5147) (root 8) 4 2) DegreeTwoThreeSpectrum6144.graph sourceMap5147swap=true := by decide +kernel
theorem fusedMap5147swap_checked : acceptsGraphIso
    (fused (graph core5147) (root 8) 4 2) DegreeTwoThreeSpectrum5195.graph fusedMap5147swap=true := by decide +kernel
theorem certified5147swap : Certified (graph core5147) (root 8) 4 2 :=
  of_native_maps core5147 DegreeTwoThreeSpectrum6144.graph DegreeTwoThreeSpectrum5195.graph
    sourceMap5147swap fusedMap5147swap sourceMap5147swap_checked fusedMap5147swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5147
#print axioms sourceMap5147swap_checked
#print axioms fusedMap5147swap_checked
#print axioms certified5147swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
