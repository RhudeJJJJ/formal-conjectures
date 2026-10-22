/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3032 : Family 10 := level10.get ⟨1641,by decide⟩
def sourceMap3032 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3032 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3032_checked : acceptsGraphIso
    (source (graph core3032) (root 10) 0 4) DegreeTwoThreeSpectrum7198.graph sourceMap3032=true := by decide +kernel
theorem fusedMap3032_checked : acceptsGraphIso
    (fused (graph core3032) (root 10) 0 4) DegreeTwoThreeSpectrum6217.graph fusedMap3032=true := by decide +kernel
theorem certified3032 : Certified (graph core3032) (root 10) 0 4 :=
  of_native_maps core3032 DegreeTwoThreeSpectrum7198.graph DegreeTwoThreeSpectrum6217.graph
    sourceMap3032 fusedMap3032 sourceMap3032_checked fusedMap3032_checked
    DegreeTwoThreeFiniteComparisons.comparison3032
#print axioms sourceMap3032_checked
#print axioms fusedMap3032_checked
#print axioms certified3032
def sourceMap3032swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3032swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3032swap_checked : acceptsGraphIso
    (source (graph core3032) (root 10) 4 0) DegreeTwoThreeSpectrum7198.graph sourceMap3032swap=true := by decide +kernel
theorem fusedMap3032swap_checked : acceptsGraphIso
    (fused (graph core3032) (root 10) 4 0) DegreeTwoThreeSpectrum6217.graph fusedMap3032swap=true := by decide +kernel
theorem certified3032swap : Certified (graph core3032) (root 10) 4 0 :=
  of_native_maps core3032 DegreeTwoThreeSpectrum7198.graph DegreeTwoThreeSpectrum6217.graph
    sourceMap3032swap fusedMap3032swap sourceMap3032swap_checked fusedMap3032swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3032
#print axioms sourceMap3032swap_checked
#print axioms fusedMap3032swap_checked
#print axioms certified3032swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
