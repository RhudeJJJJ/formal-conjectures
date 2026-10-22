/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0915 : Family 10 := level10.get ⟨706,by decide⟩
def sourceMap0915 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0915 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0915_checked : acceptsGraphIso
    (source (graph core0915) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2178.graph sourceMap0915=true := by decide +kernel
theorem fusedMap0915_checked : acceptsGraphIso
    (fused (graph core0915) (root 10) 2 2) DegreeTwoThreeSpectrum5447.graph fusedMap0915=true := by decide +kernel
theorem certified0915 : Certified (graph core0915) (root 10) 2 2 :=
  of_native_maps core0915 DegreeOneMiddleResidualSpectrum2178.graph DegreeTwoThreeSpectrum5447.graph
    sourceMap0915 fusedMap0915 sourceMap0915_checked fusedMap0915_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0915
#print axioms sourceMap0915_checked
#print axioms fusedMap0915_checked
#print axioms certified0915
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
