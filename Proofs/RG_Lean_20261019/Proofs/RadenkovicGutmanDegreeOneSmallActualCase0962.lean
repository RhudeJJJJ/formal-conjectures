/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0962 : Family 8 := level8.get ⟨78,by decide⟩
def sourceMap0962 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0962 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0962_checked : acceptsGraphIso
    (source (graph core0962) (root 8) 1 1) DegreeOneSmallSpectrum1318.graph sourceMap0962=true := by decide +kernel
theorem fusedMap0962_checked : acceptsGraphIso
    (fused (graph core0962) (root 8) 1 1) DegreeOneSmallSpectrum957.graph fusedMap0962=true := by decide +kernel
theorem certified0962 : Certified (graph core0962) (root 8) 1 1 :=
  of_native_maps core0962 DegreeOneSmallSpectrum1318.graph DegreeOneSmallSpectrum957.graph
    sourceMap0962 fusedMap0962 sourceMap0962_checked fusedMap0962_checked
    DegreeOneSmallComparisons.comparison0962
#print axioms sourceMap0962_checked
#print axioms fusedMap0962_checked
#print axioms certified0962
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
