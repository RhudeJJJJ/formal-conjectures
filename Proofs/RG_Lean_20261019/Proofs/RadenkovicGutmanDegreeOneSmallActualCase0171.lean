/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0171 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0171 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,4,5,6,7,2,3] (sourceLabel 5 0 0 v)
def fusedMap0171 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![5,0,1,2,3,4,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap0171_checked : acceptsGraphIso
    (source (graph core0171) (root 5) 0 0) DegreeOneSmallSpectrum019.graph sourceMap0171=true := by decide +kernel
theorem fusedMap0171_checked : acceptsGraphIso
    (fused (graph core0171) (root 5) 0 0) DegreeOneSmallSpectrum021.graph fusedMap0171=true := by decide +kernel
theorem certified0171 : Certified (graph core0171) (root 5) 0 0 :=
  of_native_maps core0171 DegreeOneSmallSpectrum019.graph DegreeOneSmallSpectrum021.graph
    sourceMap0171 fusedMap0171 sourceMap0171_checked fusedMap0171_checked
    DegreeOneSmallComparisons.comparison0171
#print axioms sourceMap0171_checked
#print axioms fusedMap0171_checked
#print axioms certified0171
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
