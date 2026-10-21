/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0215 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0215 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 1 3 v)
def fusedMap0215 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0215_checked : acceptsGraphIso
    (source (graph core0215) (root 5) 1 3) DegreeOneSmallSpectrum412.graph sourceMap0215=true := by decide +kernel
theorem fusedMap0215_checked : acceptsGraphIso
    (fused (graph core0215) (root 5) 1 3) DegreeOneSmallSpectrum370.graph fusedMap0215=true := by decide +kernel
theorem certified0215 : Certified (graph core0215) (root 5) 1 3 :=
  of_native_maps core0215 DegreeOneSmallSpectrum412.graph DegreeOneSmallSpectrum370.graph
    sourceMap0215 fusedMap0215 sourceMap0215_checked fusedMap0215_checked
    DegreeOneSmallComparisons.comparison0215
#print axioms sourceMap0215_checked
#print axioms fusedMap0215_checked
#print axioms certified0215
def sourceMap0215swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (sourceLabel 5 3 1 v)
def fusedMap0215swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0215swap_checked : acceptsGraphIso
    (source (graph core0215) (root 5) 3 1) DegreeOneSmallSpectrum412.graph sourceMap0215swap=true := by decide +kernel
theorem fusedMap0215swap_checked : acceptsGraphIso
    (fused (graph core0215) (root 5) 3 1) DegreeOneSmallSpectrum370.graph fusedMap0215swap=true := by decide +kernel
theorem certified0215swap : Certified (graph core0215) (root 5) 3 1 :=
  of_native_maps core0215 DegreeOneSmallSpectrum412.graph DegreeOneSmallSpectrum370.graph
    sourceMap0215swap fusedMap0215swap sourceMap0215swap_checked fusedMap0215swap_checked
    DegreeOneSmallComparisons.comparison0215
#print axioms sourceMap0215swap_checked
#print axioms fusedMap0215swap_checked
#print axioms certified0215swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
