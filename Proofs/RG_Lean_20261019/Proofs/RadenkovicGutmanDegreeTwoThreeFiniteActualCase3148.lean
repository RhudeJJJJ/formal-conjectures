/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3148 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap3148 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3148 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3148_checked : acceptsGraphIso
    (source (graph core3148) (root 8) 0 5) DegreeTwoThreeSpectrum3937.graph sourceMap3148=true := by decide +kernel
theorem fusedMap3148_checked : acceptsGraphIso
    (fused (graph core3148) (root 8) 0 5) DegreeTwoThreeSpectrum3938.graph fusedMap3148=true := by decide +kernel
theorem certified3148 : Certified (graph core3148) (root 8) 0 5 :=
  of_native_maps core3148 DegreeTwoThreeSpectrum3937.graph DegreeTwoThreeSpectrum3938.graph
    sourceMap3148 fusedMap3148 sourceMap3148_checked fusedMap3148_checked
    DegreeTwoThreeFiniteComparisons.comparison3148
#print axioms sourceMap3148_checked
#print axioms fusedMap3148_checked
#print axioms certified3148
def sourceMap3148swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3148swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3148swap_checked : acceptsGraphIso
    (source (graph core3148) (root 8) 5 0) DegreeTwoThreeSpectrum3937.graph sourceMap3148swap=true := by decide +kernel
theorem fusedMap3148swap_checked : acceptsGraphIso
    (fused (graph core3148) (root 8) 5 0) DegreeTwoThreeSpectrum3938.graph fusedMap3148swap=true := by decide +kernel
theorem certified3148swap : Certified (graph core3148) (root 8) 5 0 :=
  of_native_maps core3148 DegreeTwoThreeSpectrum3937.graph DegreeTwoThreeSpectrum3938.graph
    sourceMap3148swap fusedMap3148swap sourceMap3148swap_checked fusedMap3148swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3148
#print axioms sourceMap3148swap_checked
#print axioms fusedMap3148swap_checked
#print axioms certified3148swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
