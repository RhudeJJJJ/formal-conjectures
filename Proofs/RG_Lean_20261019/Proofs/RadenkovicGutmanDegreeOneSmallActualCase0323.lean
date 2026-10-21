/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0323 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0323 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0323 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0323_checked : acceptsGraphIso
    (source (graph core0323) (root 6) 0 2) DegreeOneSmallSpectrum181.graph sourceMap0323=true := by decide +kernel
theorem fusedMap0323_checked : acceptsGraphIso
    (fused (graph core0323) (root 6) 0 2) DegreeOneSmallSpectrum182.graph fusedMap0323=true := by decide +kernel
theorem certified0323 : Certified (graph core0323) (root 6) 0 2 :=
  of_native_maps core0323 DegreeOneSmallSpectrum181.graph DegreeOneSmallSpectrum182.graph
    sourceMap0323 fusedMap0323 sourceMap0323_checked fusedMap0323_checked
    DegreeOneSmallComparisons.comparison0323
#print axioms sourceMap0323_checked
#print axioms fusedMap0323_checked
#print axioms certified0323
def sourceMap0323swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0323swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0323swap_checked : acceptsGraphIso
    (source (graph core0323) (root 6) 2 0) DegreeOneSmallSpectrum181.graph sourceMap0323swap=true := by decide +kernel
theorem fusedMap0323swap_checked : acceptsGraphIso
    (fused (graph core0323) (root 6) 2 0) DegreeOneSmallSpectrum182.graph fusedMap0323swap=true := by decide +kernel
theorem certified0323swap : Certified (graph core0323) (root 6) 2 0 :=
  of_native_maps core0323 DegreeOneSmallSpectrum181.graph DegreeOneSmallSpectrum182.graph
    sourceMap0323swap fusedMap0323swap sourceMap0323swap_checked fusedMap0323swap_checked
    DegreeOneSmallComparisons.comparison0323
#print axioms sourceMap0323swap_checked
#print axioms fusedMap0323swap_checked
#print axioms certified0323swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
