/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3856 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap3856 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3856 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3856_checked : acceptsGraphIso
    (source (graph core3856) (root 8) 1 4) DegreeTwoThreeSpectrum4254.graph sourceMap3856=true := by decide +kernel
theorem fusedMap3856_checked : acceptsGraphIso
    (fused (graph core3856) (root 8) 1 4) DegreeTwoThreeSpectrum3908.graph fusedMap3856=true := by decide +kernel
theorem certified3856 : Certified (graph core3856) (root 8) 1 4 :=
  of_native_maps core3856 DegreeTwoThreeSpectrum4254.graph DegreeTwoThreeSpectrum3908.graph
    sourceMap3856 fusedMap3856 sourceMap3856_checked fusedMap3856_checked
    DegreeTwoThreeFiniteComparisons.comparison3856
#print axioms sourceMap3856_checked
#print axioms fusedMap3856_checked
#print axioms certified3856
def sourceMap3856swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3856swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3856swap_checked : acceptsGraphIso
    (source (graph core3856) (root 8) 4 1) DegreeTwoThreeSpectrum4254.graph sourceMap3856swap=true := by decide +kernel
theorem fusedMap3856swap_checked : acceptsGraphIso
    (fused (graph core3856) (root 8) 4 1) DegreeTwoThreeSpectrum3908.graph fusedMap3856swap=true := by decide +kernel
theorem certified3856swap : Certified (graph core3856) (root 8) 4 1 :=
  of_native_maps core3856 DegreeTwoThreeSpectrum4254.graph DegreeTwoThreeSpectrum3908.graph
    sourceMap3856swap fusedMap3856swap sourceMap3856swap_checked fusedMap3856swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3856
#print axioms sourceMap3856swap_checked
#print axioms fusedMap3856swap_checked
#print axioms certified3856swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
