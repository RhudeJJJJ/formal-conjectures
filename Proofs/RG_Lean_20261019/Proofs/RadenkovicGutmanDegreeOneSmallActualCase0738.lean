/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0738 : Family 8 := level8.get ⟨0,by decide⟩
def sourceMap0738 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,4,5,6,7] (sourceLabel 8 1 1 v)
def fusedMap0738 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 8 1 1 v)
theorem sourceMap0738_checked : acceptsGraphIso
    (source (graph core0738) (root 8) 1 1) DegreeOneSmallSpectrum915.graph sourceMap0738=true := by decide +kernel
theorem fusedMap0738_checked : acceptsGraphIso
    (fused (graph core0738) (root 8) 1 1) DegreeOneSmallSpectrum861.graph fusedMap0738=true := by decide +kernel
theorem certified0738 : Certified (graph core0738) (root 8) 1 1 :=
  of_native_maps core0738 DegreeOneSmallSpectrum915.graph DegreeOneSmallSpectrum861.graph
    sourceMap0738 fusedMap0738 sourceMap0738_checked fusedMap0738_checked
    DegreeOneSmallComparisons.comparison0738
#print axioms sourceMap0738_checked
#print axioms fusedMap0738_checked
#print axioms certified0738
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
