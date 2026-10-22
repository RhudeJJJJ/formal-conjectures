/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3629 : Family 8 := level8.get ⟨250,by decide⟩
def sourceMap3629 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3629 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3629_checked : acceptsGraphIso
    (source (graph core3629) (root 8) 0 6) DegreeTwoThreeSpectrum6688.graph sourceMap3629=true := by decide +kernel
theorem fusedMap3629_checked : acceptsGraphIso
    (fused (graph core3629) (root 8) 0 6) DegreeTwoThreeSpectrum5545.graph fusedMap3629=true := by decide +kernel
theorem certified3629 : Certified (graph core3629) (root 8) 0 6 :=
  of_native_maps core3629 DegreeTwoThreeSpectrum6688.graph DegreeTwoThreeSpectrum5545.graph
    sourceMap3629 fusedMap3629 sourceMap3629_checked fusedMap3629_checked
    DegreeTwoThreeFiniteComparisons.comparison3629
#print axioms sourceMap3629_checked
#print axioms fusedMap3629_checked
#print axioms certified3629
def sourceMap3629swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3629swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3629swap_checked : acceptsGraphIso
    (source (graph core3629) (root 8) 6 0) DegreeTwoThreeSpectrum6688.graph sourceMap3629swap=true := by decide +kernel
theorem fusedMap3629swap_checked : acceptsGraphIso
    (fused (graph core3629) (root 8) 6 0) DegreeTwoThreeSpectrum5545.graph fusedMap3629swap=true := by decide +kernel
theorem certified3629swap : Certified (graph core3629) (root 8) 6 0 :=
  of_native_maps core3629 DegreeTwoThreeSpectrum6688.graph DegreeTwoThreeSpectrum5545.graph
    sourceMap3629swap fusedMap3629swap sourceMap3629swap_checked fusedMap3629swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3629
#print axioms sourceMap3629swap_checked
#print axioms fusedMap3629swap_checked
#print axioms certified3629swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
