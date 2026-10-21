/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0775 : Family 8 := level8.get ⟨11,by decide⟩
def sourceMap0775 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0775 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0775_checked : acceptsGraphIso
    (source (graph core0775) (root 8) 0 0) DegreeOneSmallSpectrum185.graph sourceMap0775=true := by decide +kernel
theorem fusedMap0775_checked : acceptsGraphIso
    (fused (graph core0775) (root 8) 0 0) DegreeOneSmallSpectrum197.graph fusedMap0775=true := by decide +kernel
theorem certified0775 : Certified (graph core0775) (root 8) 0 0 :=
  of_native_maps core0775 DegreeOneSmallSpectrum185.graph DegreeOneSmallSpectrum197.graph
    sourceMap0775 fusedMap0775 sourceMap0775_checked fusedMap0775_checked
    DegreeOneSmallComparisons.comparison0775
#print axioms sourceMap0775_checked
#print axioms fusedMap0775_checked
#print axioms certified0775
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
