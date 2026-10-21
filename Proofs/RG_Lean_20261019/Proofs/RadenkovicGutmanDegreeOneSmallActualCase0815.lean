/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0815 : Family 8 := level8.get ⟨23,by decide⟩
def sourceMap0815 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0815 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0815_checked : acceptsGraphIso
    (source (graph core0815) (root 8) 0 0) DegreeOneSmallSpectrum181.graph sourceMap0815=true := by decide +kernel
theorem fusedMap0815_checked : acceptsGraphIso
    (fused (graph core0815) (root 8) 0 0) DegreeOneSmallSpectrum226.graph fusedMap0815=true := by decide +kernel
theorem certified0815 : Certified (graph core0815) (root 8) 0 0 :=
  of_native_maps core0815 DegreeOneSmallSpectrum181.graph DegreeOneSmallSpectrum226.graph
    sourceMap0815 fusedMap0815 sourceMap0815_checked fusedMap0815_checked
    DegreeOneSmallComparisons.comparison0815
#print axioms sourceMap0815_checked
#print axioms fusedMap0815_checked
#print axioms certified0815
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
