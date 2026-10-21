/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0961 : Family 8 := level8.get ⟨78,by decide⟩
def sourceMap0961 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0961 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0961_checked : acceptsGraphIso
    (source (graph core0961) (root 8) 0 2) DegreeOneSmallSpectrum1502.graph sourceMap0961=true := by decide +kernel
theorem fusedMap0961_checked : acceptsGraphIso
    (fused (graph core0961) (root 8) 0 2) DegreeOneSmallSpectrum957.graph fusedMap0961=true := by decide +kernel
theorem certified0961 : Certified (graph core0961) (root 8) 0 2 :=
  of_native_maps core0961 DegreeOneSmallSpectrum1502.graph DegreeOneSmallSpectrum957.graph
    sourceMap0961 fusedMap0961 sourceMap0961_checked fusedMap0961_checked
    DegreeOneSmallComparisons.comparison0961
#print axioms sourceMap0961_checked
#print axioms fusedMap0961_checked
#print axioms certified0961
def sourceMap0961swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0961swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0961swap_checked : acceptsGraphIso
    (source (graph core0961) (root 8) 2 0) DegreeOneSmallSpectrum1502.graph sourceMap0961swap=true := by decide +kernel
theorem fusedMap0961swap_checked : acceptsGraphIso
    (fused (graph core0961) (root 8) 2 0) DegreeOneSmallSpectrum957.graph fusedMap0961swap=true := by decide +kernel
theorem certified0961swap : Certified (graph core0961) (root 8) 2 0 :=
  of_native_maps core0961 DegreeOneSmallSpectrum1502.graph DegreeOneSmallSpectrum957.graph
    sourceMap0961swap fusedMap0961swap sourceMap0961swap_checked fusedMap0961swap_checked
    DegreeOneSmallComparisons.comparison0961
#print axioms sourceMap0961swap_checked
#print axioms fusedMap0961swap_checked
#print axioms certified0961swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
