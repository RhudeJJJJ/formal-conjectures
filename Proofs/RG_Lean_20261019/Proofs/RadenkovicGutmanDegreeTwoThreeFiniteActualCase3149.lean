/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3149 : Family 8 := level8.get ⟨47,by decide⟩
def sourceMap3149 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3149 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3149_checked : acceptsGraphIso
    (source (graph core3149) (root 8) 0 5) DegreeTwoThreeSpectrum3955.graph sourceMap3149=true := by decide +kernel
theorem fusedMap3149_checked : acceptsGraphIso
    (fused (graph core3149) (root 8) 0 5) DegreeTwoThreeSpectrum3956.graph fusedMap3149=true := by decide +kernel
theorem certified3149 : Certified (graph core3149) (root 8) 0 5 :=
  of_native_maps core3149 DegreeTwoThreeSpectrum3955.graph DegreeTwoThreeSpectrum3956.graph
    sourceMap3149 fusedMap3149 sourceMap3149_checked fusedMap3149_checked
    DegreeTwoThreeFiniteComparisons.comparison3149
#print axioms sourceMap3149_checked
#print axioms fusedMap3149_checked
#print axioms certified3149
def sourceMap3149swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3149swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3149swap_checked : acceptsGraphIso
    (source (graph core3149) (root 8) 5 0) DegreeTwoThreeSpectrum3955.graph sourceMap3149swap=true := by decide +kernel
theorem fusedMap3149swap_checked : acceptsGraphIso
    (fused (graph core3149) (root 8) 5 0) DegreeTwoThreeSpectrum3956.graph fusedMap3149swap=true := by decide +kernel
theorem certified3149swap : Certified (graph core3149) (root 8) 5 0 :=
  of_native_maps core3149 DegreeTwoThreeSpectrum3955.graph DegreeTwoThreeSpectrum3956.graph
    sourceMap3149swap fusedMap3149swap sourceMap3149swap_checked fusedMap3149swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3149
#print axioms sourceMap3149swap_checked
#print axioms fusedMap3149swap_checked
#print axioms certified3149swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
