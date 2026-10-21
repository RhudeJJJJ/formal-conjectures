/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0915 : Family 8 := level8.get ⟨61,by decide⟩
def sourceMap0915 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0915 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0915_checked : acceptsGraphIso
    (source (graph core0915) (root 8) 0 0) DegreeOneSmallSpectrum310.graph sourceMap0915=true := by decide +kernel
theorem fusedMap0915_checked : acceptsGraphIso
    (fused (graph core0915) (root 8) 0 0) DegreeOneSmallSpectrum208.graph fusedMap0915=true := by decide +kernel
theorem certified0915 : Certified (graph core0915) (root 8) 0 0 :=
  of_native_maps core0915 DegreeOneSmallSpectrum310.graph DegreeOneSmallSpectrum208.graph
    sourceMap0915 fusedMap0915 sourceMap0915_checked fusedMap0915_checked
    DegreeOneSmallComparisons.comparison0915
#print axioms sourceMap0915_checked
#print axioms fusedMap0915_checked
#print axioms certified0915
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
