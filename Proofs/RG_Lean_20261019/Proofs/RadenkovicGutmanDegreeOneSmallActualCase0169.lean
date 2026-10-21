/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0169 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0169 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 5 2 2 v)
def fusedMap0169 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0169_checked : acceptsGraphIso
    (source (graph core0169) (root 5) 2 2) DegreeOneSmallSpectrum563.graph sourceMap0169=true := by decide +kernel
theorem fusedMap0169_checked : acceptsGraphIso
    (fused (graph core0169) (root 5) 2 2) DegreeOneSmallSpectrum369.graph fusedMap0169=true := by decide +kernel
theorem certified0169 : Certified (graph core0169) (root 5) 2 2 :=
  of_native_maps core0169 DegreeOneSmallSpectrum563.graph DegreeOneSmallSpectrum369.graph
    sourceMap0169 fusedMap0169 sourceMap0169_checked fusedMap0169_checked
    DegreeOneSmallComparisons.comparison0169
#print axioms sourceMap0169_checked
#print axioms fusedMap0169_checked
#print axioms certified0169
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
