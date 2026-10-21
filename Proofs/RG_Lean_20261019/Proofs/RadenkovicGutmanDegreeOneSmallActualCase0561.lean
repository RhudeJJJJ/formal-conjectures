/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0561 : Family 7 := level7.get ⟨26,by decide⟩
def sourceMap0561 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (sourceLabel 7 0 0 v)
def fusedMap0561 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0561_checked : acceptsGraphIso
    (source (graph core0561) (root 7) 0 0) DegreeOneSmallSpectrum094.graph sourceMap0561=true := by decide +kernel
theorem fusedMap0561_checked : acceptsGraphIso
    (fused (graph core0561) (root 7) 0 0) SmallGeFourSpectrum016.graph fusedMap0561=true := by decide +kernel
theorem certified0561 : Certified (graph core0561) (root 7) 0 0 :=
  of_native_maps core0561 DegreeOneSmallSpectrum094.graph SmallGeFourSpectrum016.graph
    sourceMap0561 fusedMap0561 sourceMap0561_checked fusedMap0561_checked
    DegreeOneSmallComparisons.comparison0561
#print axioms sourceMap0561_checked
#print axioms fusedMap0561_checked
#print axioms certified0561
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
