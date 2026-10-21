/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0145 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0145 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 0 2 v)
def fusedMap0145 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap0145_checked : acceptsGraphIso
    (source (graph core0145) (root 4) 0 2) DegreeOneSmallSpectrum039.graph sourceMap0145=true := by decide +kernel
theorem fusedMap0145_checked : acceptsGraphIso
    (fused (graph core0145) (root 4) 0 2) DegreeOneSmallSpectrum042.graph fusedMap0145=true := by decide +kernel
theorem certified0145 : Certified (graph core0145) (root 4) 0 2 :=
  of_native_maps core0145 DegreeOneSmallSpectrum039.graph DegreeOneSmallSpectrum042.graph
    sourceMap0145 fusedMap0145 sourceMap0145_checked fusedMap0145_checked
    DegreeOneSmallComparisons.comparison0145
#print axioms sourceMap0145_checked
#print axioms fusedMap0145_checked
#print axioms certified0145
def sourceMap0145swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,6,7,8,5] (sourceLabel 4 2 0 v)
def fusedMap0145swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap0145swap_checked : acceptsGraphIso
    (source (graph core0145) (root 4) 2 0) DegreeOneSmallSpectrum039.graph sourceMap0145swap=true := by decide +kernel
theorem fusedMap0145swap_checked : acceptsGraphIso
    (fused (graph core0145) (root 4) 2 0) DegreeOneSmallSpectrum042.graph fusedMap0145swap=true := by decide +kernel
theorem certified0145swap : Certified (graph core0145) (root 4) 2 0 :=
  of_native_maps core0145 DegreeOneSmallSpectrum039.graph DegreeOneSmallSpectrum042.graph
    sourceMap0145swap fusedMap0145swap sourceMap0145swap_checked fusedMap0145swap_checked
    DegreeOneSmallComparisons.comparison0145
#print axioms sourceMap0145swap_checked
#print axioms fusedMap0145swap_checked
#print axioms certified0145swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
