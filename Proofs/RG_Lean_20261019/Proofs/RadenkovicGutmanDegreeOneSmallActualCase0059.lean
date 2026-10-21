/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0059 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0059 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (sourceLabel 3 0 4 v)
def fusedMap0059 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![1,2,3,4,0,5,6,7,8,9] (fusedLabel 3 0 4 v)
theorem sourceMap0059_checked : acceptsGraphIso
    (source (graph core0059) (root 3) 0 4) DegreeOneSmallSpectrum090.graph sourceMap0059=true := by decide +kernel
theorem fusedMap0059_checked : acceptsGraphIso
    (fused (graph core0059) (root 3) 0 4) DegreeOneSmallSpectrum073.graph fusedMap0059=true := by decide +kernel
theorem certified0059 : Certified (graph core0059) (root 3) 0 4 :=
  of_native_maps core0059 DegreeOneSmallSpectrum090.graph DegreeOneSmallSpectrum073.graph
    sourceMap0059 fusedMap0059 sourceMap0059_checked fusedMap0059_checked
    DegreeOneSmallComparisons.comparison0059
#print axioms sourceMap0059_checked
#print axioms fusedMap0059_checked
#print axioms certified0059
def sourceMap0059swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,2,3,4,0,6,7,8,9,5] (sourceLabel 3 4 0 v)
def fusedMap0059swap : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![1,2,3,4,0,5,6,7,8,9] (fusedLabel 3 4 0 v)
theorem sourceMap0059swap_checked : acceptsGraphIso
    (source (graph core0059) (root 3) 4 0) DegreeOneSmallSpectrum090.graph sourceMap0059swap=true := by decide +kernel
theorem fusedMap0059swap_checked : acceptsGraphIso
    (fused (graph core0059) (root 3) 4 0) DegreeOneSmallSpectrum073.graph fusedMap0059swap=true := by decide +kernel
theorem certified0059swap : Certified (graph core0059) (root 3) 4 0 :=
  of_native_maps core0059 DegreeOneSmallSpectrum090.graph DegreeOneSmallSpectrum073.graph
    sourceMap0059swap fusedMap0059swap sourceMap0059swap_checked fusedMap0059swap_checked
    DegreeOneSmallComparisons.comparison0059
#print axioms sourceMap0059swap_checked
#print axioms fusedMap0059swap_checked
#print axioms certified0059swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
