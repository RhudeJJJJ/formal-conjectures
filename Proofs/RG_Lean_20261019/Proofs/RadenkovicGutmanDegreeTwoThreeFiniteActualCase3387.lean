/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3387 : Family 9 := level9.get ⟨466,by decide⟩
def sourceMap3387 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3387 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3387_checked : acceptsGraphIso
    (source (graph core3387) (root 9) 0 5) DegreeTwoThreeSpectrum6703.graph sourceMap3387=true := by decide +kernel
theorem fusedMap3387_checked : acceptsGraphIso
    (fused (graph core3387) (root 9) 0 5) DegreeTwoThreeSpectrum5550.graph fusedMap3387=true := by decide +kernel
theorem certified3387 : Certified (graph core3387) (root 9) 0 5 :=
  of_native_maps core3387 DegreeTwoThreeSpectrum6703.graph DegreeTwoThreeSpectrum5550.graph
    sourceMap3387 fusedMap3387 sourceMap3387_checked fusedMap3387_checked
    DegreeTwoThreeFiniteComparisons.comparison3387
#print axioms sourceMap3387_checked
#print axioms fusedMap3387_checked
#print axioms certified3387
def sourceMap3387swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3387swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3387swap_checked : acceptsGraphIso
    (source (graph core3387) (root 9) 5 0) DegreeTwoThreeSpectrum6703.graph sourceMap3387swap=true := by decide +kernel
theorem fusedMap3387swap_checked : acceptsGraphIso
    (fused (graph core3387) (root 9) 5 0) DegreeTwoThreeSpectrum5550.graph fusedMap3387swap=true := by decide +kernel
theorem certified3387swap : Certified (graph core3387) (root 9) 5 0 :=
  of_native_maps core3387 DegreeTwoThreeSpectrum6703.graph DegreeTwoThreeSpectrum5550.graph
    sourceMap3387swap fusedMap3387swap sourceMap3387swap_checked fusedMap3387swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3387
#print axioms sourceMap3387swap_checked
#print axioms fusedMap3387swap_checked
#print axioms certified3387swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
