/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5194 : Family 8 := level8.get ⟨218,by decide⟩
def sourceMap5194 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5194 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5194_checked : acceptsGraphIso
    (source (graph core5194) (root 8) 2 4) DegreeTwoThreeSpectrum7234.graph sourceMap5194=true := by decide +kernel
theorem fusedMap5194_checked : acceptsGraphIso
    (fused (graph core5194) (root 8) 2 4) DegreeTwoThreeSpectrum5264.graph fusedMap5194=true := by decide +kernel
theorem certified5194 : Certified (graph core5194) (root 8) 2 4 :=
  of_native_maps core5194 DegreeTwoThreeSpectrum7234.graph DegreeTwoThreeSpectrum5264.graph
    sourceMap5194 fusedMap5194 sourceMap5194_checked fusedMap5194_checked
    DegreeTwoThreeFiniteComparisons.comparison5194
#print axioms sourceMap5194_checked
#print axioms fusedMap5194_checked
#print axioms certified5194
def sourceMap5194swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,13,14,15,16,10,11,12] (sourceLabel 8 4 2 v)
def fusedMap5194swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5194swap_checked : acceptsGraphIso
    (source (graph core5194) (root 8) 4 2) DegreeTwoThreeSpectrum7234.graph sourceMap5194swap=true := by decide +kernel
theorem fusedMap5194swap_checked : acceptsGraphIso
    (fused (graph core5194) (root 8) 4 2) DegreeTwoThreeSpectrum5264.graph fusedMap5194swap=true := by decide +kernel
theorem certified5194swap : Certified (graph core5194) (root 8) 4 2 :=
  of_native_maps core5194 DegreeTwoThreeSpectrum7234.graph DegreeTwoThreeSpectrum5264.graph
    sourceMap5194swap fusedMap5194swap sourceMap5194swap_checked fusedMap5194swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5194
#print axioms sourceMap5194swap_checked
#print axioms fusedMap5194swap_checked
#print axioms certified5194swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
