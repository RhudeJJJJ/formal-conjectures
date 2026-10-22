/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3547 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap3547 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3547 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3547_checked : acceptsGraphIso
    (source (graph core3547) (root 8) 0 6) DegreeTwoThreeSpectrum5298.graph sourceMap3547=true := by decide +kernel
theorem fusedMap3547_checked : acceptsGraphIso
    (fused (graph core3547) (root 8) 0 6) DegreeTwoThreeSpectrum4977.graph fusedMap3547=true := by decide +kernel
theorem certified3547 : Certified (graph core3547) (root 8) 0 6 :=
  of_native_maps core3547 DegreeTwoThreeSpectrum5298.graph DegreeTwoThreeSpectrum4977.graph
    sourceMap3547 fusedMap3547 sourceMap3547_checked fusedMap3547_checked
    DegreeTwoThreeFiniteComparisons.comparison3547
#print axioms sourceMap3547_checked
#print axioms fusedMap3547_checked
#print axioms certified3547
def sourceMap3547swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3547swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3547swap_checked : acceptsGraphIso
    (source (graph core3547) (root 8) 6 0) DegreeTwoThreeSpectrum5298.graph sourceMap3547swap=true := by decide +kernel
theorem fusedMap3547swap_checked : acceptsGraphIso
    (fused (graph core3547) (root 8) 6 0) DegreeTwoThreeSpectrum4977.graph fusedMap3547swap=true := by decide +kernel
theorem certified3547swap : Certified (graph core3547) (root 8) 6 0 :=
  of_native_maps core3547 DegreeTwoThreeSpectrum5298.graph DegreeTwoThreeSpectrum4977.graph
    sourceMap3547swap fusedMap3547swap sourceMap3547swap_checked fusedMap3547swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3547
#print axioms sourceMap3547swap_checked
#print axioms fusedMap3547swap_checked
#print axioms certified3547swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
