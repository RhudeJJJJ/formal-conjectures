/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0083 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0083 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 3 1 1 v)
def fusedMap0083 : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (fusedLabel 3 1 1 v)
theorem sourceMap0083_checked : acceptsGraphIso
    (source (graph core0083) (root 3) 1 1) DegreeOneSmallSpectrum032.graph sourceMap0083=true := by decide +kernel
theorem fusedMap0083_checked : acceptsGraphIso
    (fused (graph core0083) (root 3) 1 1) DegreeOneSmallSpectrum021.graph fusedMap0083=true := by decide +kernel
theorem certified0083 : Certified (graph core0083) (root 3) 1 1 :=
  of_native_maps core0083 DegreeOneSmallSpectrum032.graph DegreeOneSmallSpectrum021.graph
    sourceMap0083 fusedMap0083 sourceMap0083_checked fusedMap0083_checked
    DegreeOneSmallComparisons.comparison0083
#print axioms sourceMap0083_checked
#print axioms fusedMap0083_checked
#print axioms certified0083
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
