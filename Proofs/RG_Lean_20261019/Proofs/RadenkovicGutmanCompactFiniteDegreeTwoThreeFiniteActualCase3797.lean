/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3797 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap3797 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3797 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3797_checked : acceptsGraphIso
    (source (graph core3797) (root 7) 1 4) DegreeTwoThreeSpectrum2545.graph sourceMap3797=true := by decide +kernel
theorem fusedMap3797_checked : acceptsGraphIso
    (fused (graph core3797) (root 7) 1 4) DegreeTwoThreeSpectrum2324.graph fusedMap3797=true := by decide +kernel
theorem certified3797 : Certified (graph core3797) (root 7) 1 4 :=
  of_native_maps core3797 DegreeTwoThreeSpectrum2545.graph DegreeTwoThreeSpectrum2324.graph
    sourceMap3797 fusedMap3797 sourceMap3797_checked fusedMap3797_checked
    DegreeTwoThreeFiniteComparisons.comparison3797
#print axioms sourceMap3797_checked
#print axioms fusedMap3797_checked
#print axioms certified3797
def sourceMap3797swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3797swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3797swap_checked : acceptsGraphIso
    (source (graph core3797) (root 7) 4 1) DegreeTwoThreeSpectrum2545.graph sourceMap3797swap=true := by decide +kernel
theorem fusedMap3797swap_checked : acceptsGraphIso
    (fused (graph core3797) (root 7) 4 1) DegreeTwoThreeSpectrum2324.graph fusedMap3797swap=true := by decide +kernel
theorem certified3797swap : Certified (graph core3797) (root 7) 4 1 :=
  of_native_maps core3797 DegreeTwoThreeSpectrum2545.graph DegreeTwoThreeSpectrum2324.graph
    sourceMap3797swap fusedMap3797swap sourceMap3797swap_checked fusedMap3797swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3797
#print axioms sourceMap3797swap_checked
#print axioms fusedMap3797swap_checked
#print axioms certified3797swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
