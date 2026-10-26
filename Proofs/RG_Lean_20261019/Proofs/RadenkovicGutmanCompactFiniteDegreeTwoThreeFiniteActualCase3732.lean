/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3732 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3732 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (sourceLabel 5 0 9 v)
def fusedMap3732 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 0 9 v)
theorem sourceMap3732_checked : acceptsGraphIso
    (source (graph core3732) (root 5) 0 9) DegreeTwoThreeSpectrum4982.graph sourceMap3732=true := by decide +kernel
theorem fusedMap3732_checked : acceptsGraphIso
    (fused (graph core3732) (root 5) 0 9) DegreeTwoThreeSpectrum4987.graph fusedMap3732=true := by decide +kernel
theorem certified3732 : Certified (graph core3732) (root 5) 0 9 :=
  of_native_maps core3732 DegreeTwoThreeSpectrum4982.graph DegreeTwoThreeSpectrum4987.graph
    sourceMap3732 fusedMap3732 sourceMap3732_checked fusedMap3732_checked
    DegreeTwoThreeFiniteComparisons.comparison3732
#print axioms sourceMap3732_checked
#print axioms fusedMap3732_checked
#print axioms certified3732
def sourceMap3732swap : (Vertices 5 ⊕ Fin 10 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 5 9 0 v)
def fusedMap3732swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 9 0 v)
theorem sourceMap3732swap_checked : acceptsGraphIso
    (source (graph core3732) (root 5) 9 0) DegreeTwoThreeSpectrum4982.graph sourceMap3732swap=true := by decide +kernel
theorem fusedMap3732swap_checked : acceptsGraphIso
    (fused (graph core3732) (root 5) 9 0) DegreeTwoThreeSpectrum4987.graph fusedMap3732swap=true := by decide +kernel
theorem certified3732swap : Certified (graph core3732) (root 5) 9 0 :=
  of_native_maps core3732 DegreeTwoThreeSpectrum4982.graph DegreeTwoThreeSpectrum4987.graph
    sourceMap3732swap fusedMap3732swap sourceMap3732swap_checked fusedMap3732swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3732
#print axioms sourceMap3732swap_checked
#print axioms fusedMap3732swap_checked
#print axioms certified3732swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
