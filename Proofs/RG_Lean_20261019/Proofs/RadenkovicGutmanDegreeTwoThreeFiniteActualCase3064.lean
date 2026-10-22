/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3064 : Family 10 := level10.get ⟨1741,by decide⟩
def sourceMap3064 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3064 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3064_checked : acceptsGraphIso
    (source (graph core3064) (root 10) 0 4) DegreeTwoThreeSpectrum7382.graph sourceMap3064=true := by decide +kernel
theorem fusedMap3064_checked : acceptsGraphIso
    (fused (graph core3064) (root 10) 0 4) DegreeTwoThreeSpectrum6587.graph fusedMap3064=true := by decide +kernel
theorem certified3064 : Certified (graph core3064) (root 10) 0 4 :=
  of_native_maps core3064 DegreeTwoThreeSpectrum7382.graph DegreeTwoThreeSpectrum6587.graph
    sourceMap3064 fusedMap3064 sourceMap3064_checked fusedMap3064_checked
    DegreeTwoThreeFiniteComparisons.comparison3064
#print axioms sourceMap3064_checked
#print axioms fusedMap3064_checked
#print axioms certified3064
def sourceMap3064swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3064swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3064swap_checked : acceptsGraphIso
    (source (graph core3064) (root 10) 4 0) DegreeTwoThreeSpectrum7382.graph sourceMap3064swap=true := by decide +kernel
theorem fusedMap3064swap_checked : acceptsGraphIso
    (fused (graph core3064) (root 10) 4 0) DegreeTwoThreeSpectrum6587.graph fusedMap3064swap=true := by decide +kernel
theorem certified3064swap : Certified (graph core3064) (root 10) 4 0 :=
  of_native_maps core3064 DegreeTwoThreeSpectrum7382.graph DegreeTwoThreeSpectrum6587.graph
    sourceMap3064swap fusedMap3064swap sourceMap3064swap_checked fusedMap3064swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3064
#print axioms sourceMap3064swap_checked
#print axioms fusedMap3064swap_checked
#print axioms certified3064swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
