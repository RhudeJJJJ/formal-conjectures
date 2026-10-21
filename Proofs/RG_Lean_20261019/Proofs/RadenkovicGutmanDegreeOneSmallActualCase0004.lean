/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0004 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0004 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 5) → Fin 8 :=
  fun v => ![2,3,4,1,0,5,6,7] (sourceLabel 1 0 4 v)
def fusedMap0004 : (Vertices 1 ⊕ Fin 6) → Fin 8 :=
  fun v => ![2,3,1,0,4,5,6,7] (fusedLabel 1 0 4 v)
theorem sourceMap0004_checked : acceptsGraphIso
    (source (graph core0004) (root 1) 0 4) DegreeOneSmallSpectrum021.graph sourceMap0004=true := by decide +kernel
theorem fusedMap0004_checked : acceptsGraphIso
    (fused (graph core0004) (root 1) 0 4) DegreeOneSmallSpectrum016.graph fusedMap0004=true := by decide +kernel
theorem certified0004 : Certified (graph core0004) (root 1) 0 4 :=
  of_native_maps core0004 DegreeOneSmallSpectrum021.graph DegreeOneSmallSpectrum016.graph
    sourceMap0004 fusedMap0004 sourceMap0004_checked fusedMap0004_checked
    DegreeOneSmallComparisons.comparison0004
#print axioms sourceMap0004_checked
#print axioms fusedMap0004_checked
#print axioms certified0004
def sourceMap0004swap : (Vertices 1 ⊕ Fin 5 ⊕ Fin 1) → Fin 8 :=
  fun v => ![2,3,1,0,5,6,7,4] (sourceLabel 1 4 0 v)
def fusedMap0004swap : (Vertices 1 ⊕ Fin 6) → Fin 8 :=
  fun v => ![2,3,1,0,4,5,6,7] (fusedLabel 1 4 0 v)
theorem sourceMap0004swap_checked : acceptsGraphIso
    (source (graph core0004) (root 1) 4 0) DegreeOneSmallSpectrum021.graph sourceMap0004swap=true := by decide +kernel
theorem fusedMap0004swap_checked : acceptsGraphIso
    (fused (graph core0004) (root 1) 4 0) DegreeOneSmallSpectrum016.graph fusedMap0004swap=true := by decide +kernel
theorem certified0004swap : Certified (graph core0004) (root 1) 4 0 :=
  of_native_maps core0004 DegreeOneSmallSpectrum021.graph DegreeOneSmallSpectrum016.graph
    sourceMap0004swap fusedMap0004swap sourceMap0004swap_checked fusedMap0004swap_checked
    DegreeOneSmallComparisons.comparison0004
#print axioms sourceMap0004swap_checked
#print axioms fusedMap0004swap_checked
#print axioms certified0004swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
