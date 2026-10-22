/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1365 : Family 9 := level9.get ⟨513,by decide⟩
def sourceMap1365 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,1,2,3,7,4,5,6] (sourceLabel 9 0 2 v)
def fusedMap1365 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1365_checked : acceptsGraphIso
    (source (graph core1365) (root 9) 0 2) DegreeTwoThreeSpectrum2184.graph sourceMap1365=true := by decide +kernel
theorem fusedMap1365_checked : acceptsGraphIso
    (fused (graph core1365) (root 9) 0 2) DegreeTwoThreeSpectrum2225.graph fusedMap1365=true := by decide +kernel
theorem certified1365 : Certified (graph core1365) (root 9) 0 2 :=
  of_native_maps core1365 DegreeTwoThreeSpectrum2184.graph DegreeTwoThreeSpectrum2225.graph
    sourceMap1365 fusedMap1365 sourceMap1365_checked fusedMap1365_checked
    DegreeTwoThreeFiniteComparisons.comparison1365
#print axioms sourceMap1365_checked
#print axioms fusedMap1365_checked
#print axioms certified1365
def sourceMap1365swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,1,2,3,4,5,6,7] (sourceLabel 9 2 0 v)
def fusedMap1365swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1365swap_checked : acceptsGraphIso
    (source (graph core1365) (root 9) 2 0) DegreeTwoThreeSpectrum2184.graph sourceMap1365swap=true := by decide +kernel
theorem fusedMap1365swap_checked : acceptsGraphIso
    (fused (graph core1365) (root 9) 2 0) DegreeTwoThreeSpectrum2225.graph fusedMap1365swap=true := by decide +kernel
theorem certified1365swap : Certified (graph core1365) (root 9) 2 0 :=
  of_native_maps core1365 DegreeTwoThreeSpectrum2184.graph DegreeTwoThreeSpectrum2225.graph
    sourceMap1365swap fusedMap1365swap sourceMap1365swap_checked fusedMap1365swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1365
#print axioms sourceMap1365swap_checked
#print axioms fusedMap1365swap_checked
#print axioms certified1365swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
