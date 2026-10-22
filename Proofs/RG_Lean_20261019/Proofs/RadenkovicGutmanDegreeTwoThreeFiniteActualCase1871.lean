/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1871 : Family 10 := level10.get ⟨1308,by decide⟩
def sourceMap1871 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1871 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1871_checked : acceptsGraphIso
    (source (graph core1871) (root 10) 0 2) DegreeTwoThreeSpectrum3475.graph sourceMap1871=true := by decide +kernel
theorem fusedMap1871_checked : acceptsGraphIso
    (fused (graph core1871) (root 10) 0 2) DegreeTwoThreeSpectrum3476.graph fusedMap1871=true := by decide +kernel
theorem certified1871 : Certified (graph core1871) (root 10) 0 2 :=
  of_native_maps core1871 DegreeTwoThreeSpectrum3475.graph DegreeTwoThreeSpectrum3476.graph
    sourceMap1871 fusedMap1871 sourceMap1871_checked fusedMap1871_checked
    DegreeTwoThreeFiniteComparisons.comparison1871
#print axioms sourceMap1871_checked
#print axioms fusedMap1871_checked
#print axioms certified1871
def sourceMap1871swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1871swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1871swap_checked : acceptsGraphIso
    (source (graph core1871) (root 10) 2 0) DegreeTwoThreeSpectrum3475.graph sourceMap1871swap=true := by decide +kernel
theorem fusedMap1871swap_checked : acceptsGraphIso
    (fused (graph core1871) (root 10) 2 0) DegreeTwoThreeSpectrum3476.graph fusedMap1871swap=true := by decide +kernel
theorem certified1871swap : Certified (graph core1871) (root 10) 2 0 :=
  of_native_maps core1871 DegreeTwoThreeSpectrum3475.graph DegreeTwoThreeSpectrum3476.graph
    sourceMap1871swap fusedMap1871swap sourceMap1871swap_checked fusedMap1871swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1871
#print axioms sourceMap1871swap_checked
#print axioms fusedMap1871swap_checked
#print axioms certified1871swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
