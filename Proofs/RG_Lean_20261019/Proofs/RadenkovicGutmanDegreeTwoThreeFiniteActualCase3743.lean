/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3743 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3743 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (sourceLabel 3 0 11 v)
def fusedMap3743 : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 0 11 v)
theorem sourceMap3743_checked : acceptsGraphIso
    (source (graph core3743) (root 3) 0 11) DegreeTwoThreeSpectrum5020.graph sourceMap3743=true := by decide +kernel
theorem fusedMap3743_checked : acceptsGraphIso
    (fused (graph core3743) (root 3) 0 11) DegreeTwoThreeSpectrum4960.graph fusedMap3743=true := by decide +kernel
theorem certified3743 : Certified (graph core3743) (root 3) 0 11 :=
  of_native_maps core3743 DegreeTwoThreeSpectrum5020.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap3743 fusedMap3743 sourceMap3743_checked fusedMap3743_checked
    DegreeTwoThreeFiniteComparisons.comparison3743
#print axioms sourceMap3743_checked
#print axioms fusedMap3743_checked
#print axioms certified3743
def sourceMap3743swap : (Vertices 3 ⊕ Fin 12 ⊕ Fin 1) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 3 11 0 v)
def fusedMap3743swap : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 11 0 v)
theorem sourceMap3743swap_checked : acceptsGraphIso
    (source (graph core3743) (root 3) 11 0) DegreeTwoThreeSpectrum5020.graph sourceMap3743swap=true := by decide +kernel
theorem fusedMap3743swap_checked : acceptsGraphIso
    (fused (graph core3743) (root 3) 11 0) DegreeTwoThreeSpectrum4960.graph fusedMap3743swap=true := by decide +kernel
theorem certified3743swap : Certified (graph core3743) (root 3) 11 0 :=
  of_native_maps core3743 DegreeTwoThreeSpectrum5020.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap3743swap fusedMap3743swap sourceMap3743swap_checked fusedMap3743swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3743
#print axioms sourceMap3743swap_checked
#print axioms fusedMap3743swap_checked
#print axioms certified3743swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
