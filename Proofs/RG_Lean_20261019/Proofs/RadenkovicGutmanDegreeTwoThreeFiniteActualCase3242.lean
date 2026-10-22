/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3242 : Family 9 := level9.get ⟨40,by decide⟩
def sourceMap3242 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6] (sourceLabel 9 0 5 v)
def fusedMap3242 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 0 5 v)
theorem sourceMap3242_checked : acceptsGraphIso
    (source (graph core3242) (root 9) 0 5) DegreeTwoThreeSpectrum5129.graph sourceMap3242=true := by decide +kernel
theorem fusedMap3242_checked : acceptsGraphIso
    (fused (graph core3242) (root 9) 0 5) DegreeTwoThreeSpectrum5132.graph fusedMap3242=true := by decide +kernel
theorem certified3242 : Certified (graph core3242) (root 9) 0 5 :=
  of_native_maps core3242 DegreeTwoThreeSpectrum5129.graph DegreeTwoThreeSpectrum5132.graph
    sourceMap3242 fusedMap3242 sourceMap3242_checked fusedMap3242_checked
    DegreeTwoThreeFiniteComparisons.comparison3242
#print axioms sourceMap3242_checked
#print axioms fusedMap3242_checked
#print axioms certified3242
def sourceMap3242swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,1,2,3,4,5,6,8] (sourceLabel 9 5 0 v)
def fusedMap3242swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 5 0 v)
theorem sourceMap3242swap_checked : acceptsGraphIso
    (source (graph core3242) (root 9) 5 0) DegreeTwoThreeSpectrum5129.graph sourceMap3242swap=true := by decide +kernel
theorem fusedMap3242swap_checked : acceptsGraphIso
    (fused (graph core3242) (root 9) 5 0) DegreeTwoThreeSpectrum5132.graph fusedMap3242swap=true := by decide +kernel
theorem certified3242swap : Certified (graph core3242) (root 9) 5 0 :=
  of_native_maps core3242 DegreeTwoThreeSpectrum5129.graph DegreeTwoThreeSpectrum5132.graph
    sourceMap3242swap fusedMap3242swap sourceMap3242swap_checked fusedMap3242swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3242
#print axioms sourceMap3242swap_checked
#print axioms fusedMap3242swap_checked
#print axioms certified3242swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
