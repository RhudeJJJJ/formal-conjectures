/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0573 : Family 7 := level7.get ⟨28,by decide⟩
def sourceMap0573 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,5,0,1,2,3,4,9,7,8] (sourceLabel 7 0 0 v)
def fusedMap0573 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0573_checked : acceptsGraphIso
    (source (graph core0573) (root 7) 0 0) DegreeOneSmallSpectrum102.graph sourceMap0573=true := by decide +kernel
theorem fusedMap0573_checked : acceptsGraphIso
    (fused (graph core0573) (root 7) 0 0) DegreeOneSmallSpectrum106.graph fusedMap0573=true := by decide +kernel
theorem certified0573 : Certified (graph core0573) (root 7) 0 0 :=
  of_native_maps core0573 DegreeOneSmallSpectrum102.graph DegreeOneSmallSpectrum106.graph
    sourceMap0573 fusedMap0573 sourceMap0573_checked fusedMap0573_checked
    DegreeOneSmallComparisons.comparison0573
#print axioms sourceMap0573_checked
#print axioms fusedMap0573_checked
#print axioms certified0573
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
