/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0365 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0365 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0365 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0365_checked : acceptsGraphIso
    (source (graph core0365) (root 6) 2 2) DegreeOneSmallSpectrum1427.graph sourceMap0365=true := by decide +kernel
theorem fusedMap0365_checked : acceptsGraphIso
    (fused (graph core0365) (root 6) 2 2) DegreeOneSmallSpectrum929.graph fusedMap0365=true := by decide +kernel
theorem certified0365 : Certified (graph core0365) (root 6) 2 2 :=
  of_native_maps core0365 DegreeOneSmallSpectrum1427.graph DegreeOneSmallSpectrum929.graph
    sourceMap0365 fusedMap0365 sourceMap0365_checked fusedMap0365_checked
    DegreeOneSmallComparisons.comparison0365
#print axioms sourceMap0365_checked
#print axioms fusedMap0365_checked
#print axioms certified0365
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
