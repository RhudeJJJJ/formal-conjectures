/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0275 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0275 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 6 2 2 v)
def fusedMap0275 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0275_checked : acceptsGraphIso
    (source (graph core0275) (root 6) 2 2) DegreeOneSmallSpectrum945.graph sourceMap0275=true := by decide +kernel
theorem fusedMap0275_checked : acceptsGraphIso
    (fused (graph core0275) (root 6) 2 2) DegreeOneSmallSpectrum861.graph fusedMap0275=true := by decide +kernel
theorem certified0275 : Certified (graph core0275) (root 6) 2 2 :=
  of_native_maps core0275 DegreeOneSmallSpectrum945.graph DegreeOneSmallSpectrum861.graph
    sourceMap0275 fusedMap0275 sourceMap0275_checked fusedMap0275_checked
    DegreeOneSmallComparisons.comparison0275
#print axioms sourceMap0275_checked
#print axioms fusedMap0275_checked
#print axioms certified0275
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
