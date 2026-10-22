/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3003 : Family 10 := level10.get ⟨1576,by decide⟩
def sourceMap3003 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3003 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3003_checked : acceptsGraphIso
    (source (graph core3003) (root 10) 0 4) DegreeTwoThreeSpectrum7114.graph sourceMap3003=true := by decide +kernel
theorem fusedMap3003_checked : acceptsGraphIso
    (fused (graph core3003) (root 10) 0 4) DegreeTwoThreeSpectrum6056.graph fusedMap3003=true := by decide +kernel
theorem certified3003 : Certified (graph core3003) (root 10) 0 4 :=
  of_native_maps core3003 DegreeTwoThreeSpectrum7114.graph DegreeTwoThreeSpectrum6056.graph
    sourceMap3003 fusedMap3003 sourceMap3003_checked fusedMap3003_checked
    DegreeTwoThreeFiniteComparisons.comparison3003
#print axioms sourceMap3003_checked
#print axioms fusedMap3003_checked
#print axioms certified3003
def sourceMap3003swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3003swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3003swap_checked : acceptsGraphIso
    (source (graph core3003) (root 10) 4 0) DegreeTwoThreeSpectrum7114.graph sourceMap3003swap=true := by decide +kernel
theorem fusedMap3003swap_checked : acceptsGraphIso
    (fused (graph core3003) (root 10) 4 0) DegreeTwoThreeSpectrum6056.graph fusedMap3003swap=true := by decide +kernel
theorem certified3003swap : Certified (graph core3003) (root 10) 4 0 :=
  of_native_maps core3003 DegreeTwoThreeSpectrum7114.graph DegreeTwoThreeSpectrum6056.graph
    sourceMap3003swap fusedMap3003swap sourceMap3003swap_checked fusedMap3003swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3003
#print axioms sourceMap3003swap_checked
#print axioms fusedMap3003swap_checked
#print axioms certified3003swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
