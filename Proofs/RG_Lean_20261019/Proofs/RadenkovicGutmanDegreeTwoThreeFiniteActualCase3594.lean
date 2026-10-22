/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3594 : Family 8 := level8.get ⟨173,by decide⟩
def sourceMap3594 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3594 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3594_checked : acceptsGraphIso
    (source (graph core3594) (root 8) 0 6) DegreeTwoThreeSpectrum5739.graph sourceMap3594=true := by decide +kernel
theorem fusedMap3594_checked : acceptsGraphIso
    (fused (graph core3594) (root 8) 0 6) DegreeTwoThreeSpectrum5741.graph fusedMap3594=true := by decide +kernel
theorem certified3594 : Certified (graph core3594) (root 8) 0 6 :=
  of_native_maps core3594 DegreeTwoThreeSpectrum5739.graph DegreeTwoThreeSpectrum5741.graph
    sourceMap3594 fusedMap3594 sourceMap3594_checked fusedMap3594_checked
    DegreeTwoThreeFiniteComparisons.comparison3594
#print axioms sourceMap3594_checked
#print axioms fusedMap3594_checked
#print axioms certified3594
def sourceMap3594swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3594swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3594swap_checked : acceptsGraphIso
    (source (graph core3594) (root 8) 6 0) DegreeTwoThreeSpectrum5739.graph sourceMap3594swap=true := by decide +kernel
theorem fusedMap3594swap_checked : acceptsGraphIso
    (fused (graph core3594) (root 8) 6 0) DegreeTwoThreeSpectrum5741.graph fusedMap3594swap=true := by decide +kernel
theorem certified3594swap : Certified (graph core3594) (root 8) 6 0 :=
  of_native_maps core3594 DegreeTwoThreeSpectrum5739.graph DegreeTwoThreeSpectrum5741.graph
    sourceMap3594swap fusedMap3594swap sourceMap3594swap_checked fusedMap3594swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3594
#print axioms sourceMap3594swap_checked
#print axioms fusedMap3594swap_checked
#print axioms certified3594swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
