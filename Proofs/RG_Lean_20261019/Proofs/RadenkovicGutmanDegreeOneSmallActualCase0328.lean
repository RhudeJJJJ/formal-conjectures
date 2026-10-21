/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0328 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0328 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0328 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0328_checked : acceptsGraphIso
    (source (graph core0328) (root 6) 1 3) DegreeOneSmallSpectrum1181.graph sourceMap0328=true := by decide +kernel
theorem fusedMap0328_checked : acceptsGraphIso
    (fused (graph core0328) (root 6) 1 3) DegreeOneSmallSpectrum879.graph fusedMap0328=true := by decide +kernel
theorem certified0328 : Certified (graph core0328) (root 6) 1 3 :=
  of_native_maps core0328 DegreeOneSmallSpectrum1181.graph DegreeOneSmallSpectrum879.graph
    sourceMap0328 fusedMap0328 sourceMap0328_checked fusedMap0328_checked
    DegreeOneSmallComparisons.comparison0328
#print axioms sourceMap0328_checked
#print axioms fusedMap0328_checked
#print axioms certified0328
def sourceMap0328swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0328swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0328swap_checked : acceptsGraphIso
    (source (graph core0328) (root 6) 3 1) DegreeOneSmallSpectrum1181.graph sourceMap0328swap=true := by decide +kernel
theorem fusedMap0328swap_checked : acceptsGraphIso
    (fused (graph core0328) (root 6) 3 1) DegreeOneSmallSpectrum879.graph fusedMap0328swap=true := by decide +kernel
theorem certified0328swap : Certified (graph core0328) (root 6) 3 1 :=
  of_native_maps core0328 DegreeOneSmallSpectrum1181.graph DegreeOneSmallSpectrum879.graph
    sourceMap0328swap fusedMap0328swap sourceMap0328swap_checked fusedMap0328swap_checked
    DegreeOneSmallComparisons.comparison0328
#print axioms sourceMap0328swap_checked
#print axioms fusedMap0328swap_checked
#print axioms certified0328swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
