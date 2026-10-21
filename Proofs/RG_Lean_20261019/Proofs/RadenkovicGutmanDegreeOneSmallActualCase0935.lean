/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0935 : Family 8 := level8.get ⟨70,by decide⟩
def sourceMap0935 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0935 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0935_checked : acceptsGraphIso
    (source (graph core0935) (root 8) 0 0) DegreeOneSmallSpectrum312.graph sourceMap0935=true := by decide +kernel
theorem fusedMap0935_checked : acceptsGraphIso
    (fused (graph core0935) (root 8) 0 0) DegreeOneSmallSpectrum218.graph fusedMap0935=true := by decide +kernel
theorem certified0935 : Certified (graph core0935) (root 8) 0 0 :=
  of_native_maps core0935 DegreeOneSmallSpectrum312.graph DegreeOneSmallSpectrum218.graph
    sourceMap0935 fusedMap0935 sourceMap0935_checked fusedMap0935_checked
    DegreeOneSmallComparisons.comparison0935
#print axioms sourceMap0935_checked
#print axioms fusedMap0935_checked
#print axioms certified0935
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
