/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0376 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0376 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (sourceLabel 6 0 1 v)
def fusedMap0376 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0376_checked : acceptsGraphIso
    (source (graph core0376) (root 6) 0 1) DegreeOneSmallSpectrum145.graph sourceMap0376=true := by decide +kernel
theorem fusedMap0376_checked : acceptsGraphIso
    (fused (graph core0376) (root 6) 0 1) DegreeOneSmallSpectrum088.graph fusedMap0376=true := by decide +kernel
theorem certified0376 : Certified (graph core0376) (root 6) 0 1 :=
  of_native_maps core0376 DegreeOneSmallSpectrum145.graph DegreeOneSmallSpectrum088.graph
    sourceMap0376 fusedMap0376 sourceMap0376_checked fusedMap0376_checked
    DegreeOneSmallComparisons.comparison0376
#print axioms sourceMap0376_checked
#print axioms fusedMap0376_checked
#print axioms certified0376
def sourceMap0376swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 6 1 0 v)
def fusedMap0376swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0376swap_checked : acceptsGraphIso
    (source (graph core0376) (root 6) 1 0) DegreeOneSmallSpectrum145.graph sourceMap0376swap=true := by decide +kernel
theorem fusedMap0376swap_checked : acceptsGraphIso
    (fused (graph core0376) (root 6) 1 0) DegreeOneSmallSpectrum088.graph fusedMap0376swap=true := by decide +kernel
theorem certified0376swap : Certified (graph core0376) (root 6) 1 0 :=
  of_native_maps core0376 DegreeOneSmallSpectrum145.graph DegreeOneSmallSpectrum088.graph
    sourceMap0376swap fusedMap0376swap sourceMap0376swap_checked fusedMap0376swap_checked
    DegreeOneSmallComparisons.comparison0376
#print axioms sourceMap0376swap_checked
#print axioms fusedMap0376swap_checked
#print axioms certified0376swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
