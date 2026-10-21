/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0927 : Family 8 := level8.get ⟨65,by decide⟩
def sourceMap0927 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0927 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0927_checked : acceptsGraphIso
    (source (graph core0927) (root 8) 0 0) DegreeOneSmallSpectrum280.graph sourceMap0927=true := by decide +kernel
theorem fusedMap0927_checked : acceptsGraphIso
    (fused (graph core0927) (root 8) 0 0) DegreeOneSmallSpectrum214.graph fusedMap0927=true := by decide +kernel
theorem certified0927 : Certified (graph core0927) (root 8) 0 0 :=
  of_native_maps core0927 DegreeOneSmallSpectrum280.graph DegreeOneSmallSpectrum214.graph
    sourceMap0927 fusedMap0927 sourceMap0927_checked fusedMap0927_checked
    DegreeOneSmallComparisons.comparison0927
#print axioms sourceMap0927_checked
#print axioms fusedMap0927_checked
#print axioms certified0927
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
