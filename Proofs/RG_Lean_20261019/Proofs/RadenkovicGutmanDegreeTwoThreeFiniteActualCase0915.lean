/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0915 : Family 10 := level10.get ⟨1478,by decide⟩
def sourceMap0915 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0915 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0915_checked : acceptsGraphIso
    (source (graph core0915) (root 10) 0 0) DegreeOneSmallSpectrum1146.graph sourceMap0915=true := by decide +kernel
theorem fusedMap0915_checked : acceptsGraphIso
    (fused (graph core0915) (root 10) 0 0) DegreeOneSmallSpectrum1141.graph fusedMap0915=true := by decide +kernel
theorem certified0915 : Certified (graph core0915) (root 10) 0 0 :=
  of_native_maps core0915 DegreeOneSmallSpectrum1146.graph DegreeOneSmallSpectrum1141.graph
    sourceMap0915 fusedMap0915 sourceMap0915_checked fusedMap0915_checked
    DegreeTwoThreeFiniteComparisons.comparison0915
#print axioms sourceMap0915_checked
#print axioms fusedMap0915_checked
#print axioms certified0915
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
