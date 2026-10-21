/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0335 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0335 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,10,6,7,8,9] (sourceLabel 6 1 1 v)
def fusedMap0335 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0335_checked : acceptsGraphIso
    (source (graph core0335) (root 6) 1 1) DegreeOneSmallSpectrum306.graph sourceMap0335=true := by decide +kernel
theorem fusedMap0335_checked : acceptsGraphIso
    (fused (graph core0335) (root 6) 1 1) DegreeOneSmallSpectrum188.graph fusedMap0335=true := by decide +kernel
theorem certified0335 : Certified (graph core0335) (root 6) 1 1 :=
  of_native_maps core0335 DegreeOneSmallSpectrum306.graph DegreeOneSmallSpectrum188.graph
    sourceMap0335 fusedMap0335 sourceMap0335_checked fusedMap0335_checked
    DegreeOneSmallComparisons.comparison0335
#print axioms sourceMap0335_checked
#print axioms fusedMap0335_checked
#print axioms certified0335
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
