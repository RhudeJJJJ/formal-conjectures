/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0099 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0099 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap0099 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap0099_checked : acceptsGraphIso
    (source (graph core0099) (root 4) 0 4) DegreeOneSmallSpectrum167.graph sourceMap0099=true := by decide +kernel
theorem fusedMap0099_checked : acceptsGraphIso
    (fused (graph core0099) (root 4) 0 4) DegreeOneSmallSpectrum168.graph fusedMap0099=true := by decide +kernel
theorem certified0099 : Certified (graph core0099) (root 4) 0 4 :=
  of_native_maps core0099 DegreeOneSmallSpectrum167.graph DegreeOneSmallSpectrum168.graph
    sourceMap0099 fusedMap0099 sourceMap0099_checked fusedMap0099_checked
    DegreeOneSmallComparisons.comparison0099
#print axioms sourceMap0099_checked
#print axioms fusedMap0099_checked
#print axioms certified0099
def sourceMap0099swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,6,7,8,9,10,5] (sourceLabel 4 4 0 v)
def fusedMap0099swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap0099swap_checked : acceptsGraphIso
    (source (graph core0099) (root 4) 4 0) DegreeOneSmallSpectrum167.graph sourceMap0099swap=true := by decide +kernel
theorem fusedMap0099swap_checked : acceptsGraphIso
    (fused (graph core0099) (root 4) 4 0) DegreeOneSmallSpectrum168.graph fusedMap0099swap=true := by decide +kernel
theorem certified0099swap : Certified (graph core0099) (root 4) 4 0 :=
  of_native_maps core0099 DegreeOneSmallSpectrum167.graph DegreeOneSmallSpectrum168.graph
    sourceMap0099swap fusedMap0099swap sourceMap0099swap_checked fusedMap0099swap_checked
    DegreeOneSmallComparisons.comparison0099
#print axioms sourceMap0099swap_checked
#print axioms fusedMap0099swap_checked
#print axioms certified0099swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
