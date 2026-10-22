/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3893 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap3893 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3893 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3893_checked : acceptsGraphIso
    (source (graph core3893) (root 8) 1 4) DegreeTwoThreeSpectrum4700.graph sourceMap3893=true := by decide +kernel
theorem fusedMap3893_checked : acceptsGraphIso
    (fused (graph core3893) (root 8) 1 4) DegreeTwoThreeSpectrum4219.graph fusedMap3893=true := by decide +kernel
theorem certified3893 : Certified (graph core3893) (root 8) 1 4 :=
  of_native_maps core3893 DegreeTwoThreeSpectrum4700.graph DegreeTwoThreeSpectrum4219.graph
    sourceMap3893 fusedMap3893 sourceMap3893_checked fusedMap3893_checked
    DegreeTwoThreeFiniteComparisons.comparison3893
#print axioms sourceMap3893_checked
#print axioms fusedMap3893_checked
#print axioms certified3893
def sourceMap3893swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3893swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3893swap_checked : acceptsGraphIso
    (source (graph core3893) (root 8) 4 1) DegreeTwoThreeSpectrum4700.graph sourceMap3893swap=true := by decide +kernel
theorem fusedMap3893swap_checked : acceptsGraphIso
    (fused (graph core3893) (root 8) 4 1) DegreeTwoThreeSpectrum4219.graph fusedMap3893swap=true := by decide +kernel
theorem certified3893swap : Certified (graph core3893) (root 8) 4 1 :=
  of_native_maps core3893 DegreeTwoThreeSpectrum4700.graph DegreeTwoThreeSpectrum4219.graph
    sourceMap3893swap fusedMap3893swap sourceMap3893swap_checked fusedMap3893swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3893
#print axioms sourceMap3893swap_checked
#print axioms fusedMap3893swap_checked
#print axioms certified3893swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
