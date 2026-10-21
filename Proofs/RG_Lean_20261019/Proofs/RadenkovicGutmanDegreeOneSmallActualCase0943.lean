/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0943 : Family 8 := level8.get ⟨72,by decide⟩
def sourceMap0943 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0943 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0943_checked : acceptsGraphIso
    (source (graph core0943) (root 8) 0 0) DegreeOneSmallSpectrum314.graph sourceMap0943=true := by decide +kernel
theorem fusedMap0943_checked : acceptsGraphIso
    (fused (graph core0943) (root 8) 0 0) DegreeOneSmallSpectrum220.graph fusedMap0943=true := by decide +kernel
theorem certified0943 : Certified (graph core0943) (root 8) 0 0 :=
  of_native_maps core0943 DegreeOneSmallSpectrum314.graph DegreeOneSmallSpectrum220.graph
    sourceMap0943 fusedMap0943 sourceMap0943_checked fusedMap0943_checked
    DegreeOneSmallComparisons.comparison0943
#print axioms sourceMap0943_checked
#print axioms fusedMap0943_checked
#print axioms certified0943
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
