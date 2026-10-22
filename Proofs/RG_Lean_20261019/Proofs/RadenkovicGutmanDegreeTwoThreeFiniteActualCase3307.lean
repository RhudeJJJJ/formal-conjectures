/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3307 : Family 9 := level9.get ⟨257,by decide⟩
def sourceMap3307 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3307 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3307_checked : acceptsGraphIso
    (source (graph core3307) (root 9) 0 5) DegreeTwoThreeSpectrum5685.graph sourceMap3307=true := by decide +kernel
theorem fusedMap3307_checked : acceptsGraphIso
    (fused (graph core3307) (root 9) 0 5) DegreeTwoThreeSpectrum5686.graph fusedMap3307=true := by decide +kernel
theorem certified3307 : Certified (graph core3307) (root 9) 0 5 :=
  of_native_maps core3307 DegreeTwoThreeSpectrum5685.graph DegreeTwoThreeSpectrum5686.graph
    sourceMap3307 fusedMap3307 sourceMap3307_checked fusedMap3307_checked
    DegreeTwoThreeFiniteComparisons.comparison3307
#print axioms sourceMap3307_checked
#print axioms fusedMap3307_checked
#print axioms certified3307
def sourceMap3307swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3307swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3307swap_checked : acceptsGraphIso
    (source (graph core3307) (root 9) 5 0) DegreeTwoThreeSpectrum5685.graph sourceMap3307swap=true := by decide +kernel
theorem fusedMap3307swap_checked : acceptsGraphIso
    (fused (graph core3307) (root 9) 5 0) DegreeTwoThreeSpectrum5686.graph fusedMap3307swap=true := by decide +kernel
theorem certified3307swap : Certified (graph core3307) (root 9) 5 0 :=
  of_native_maps core3307 DegreeTwoThreeSpectrum5685.graph DegreeTwoThreeSpectrum5686.graph
    sourceMap3307swap fusedMap3307swap sourceMap3307swap_checked fusedMap3307swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3307
#print axioms sourceMap3307swap_checked
#print axioms fusedMap3307swap_checked
#print axioms certified3307swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
