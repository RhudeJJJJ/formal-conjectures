/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0380 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0380 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0380 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0380_checked : acceptsGraphIso
    (source (graph core0380) (root 6) 1 1) DegreeOneSmallSpectrum330.graph sourceMap0380=true := by decide +kernel
theorem fusedMap0380_checked : acceptsGraphIso
    (fused (graph core0380) (root 6) 1 1) DegreeOneSmallSpectrum225.graph fusedMap0380=true := by decide +kernel
theorem certified0380 : Certified (graph core0380) (root 6) 1 1 :=
  of_native_maps core0380 DegreeOneSmallSpectrum330.graph DegreeOneSmallSpectrum225.graph
    sourceMap0380 fusedMap0380 sourceMap0380_checked fusedMap0380_checked
    DegreeOneSmallComparisons.comparison0380
#print axioms sourceMap0380_checked
#print axioms fusedMap0380_checked
#print axioms certified0380
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
