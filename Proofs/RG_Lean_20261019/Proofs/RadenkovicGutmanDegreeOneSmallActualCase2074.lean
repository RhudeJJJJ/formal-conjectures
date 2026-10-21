/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2074 : Family 10 := level10.get ⟨459,by decide⟩
def sourceMap2074 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,8,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2074 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2074_checked : acceptsGraphIso
    (source (graph core2074) (root 10) 0 0) DegreeOneSmallSpectrum1114.graph sourceMap2074=true := by decide +kernel
theorem fusedMap2074_checked : acceptsGraphIso
    (fused (graph core2074) (root 10) 0 0) DegreeOneSmallSpectrum1497.graph fusedMap2074=true := by decide +kernel
theorem certified2074 : Certified (graph core2074) (root 10) 0 0 :=
  of_native_maps core2074 DegreeOneSmallSpectrum1114.graph DegreeOneSmallSpectrum1497.graph
    sourceMap2074 fusedMap2074 sourceMap2074_checked fusedMap2074_checked
    DegreeOneSmallComparisons.comparison2074
#print axioms sourceMap2074_checked
#print axioms fusedMap2074_checked
#print axioms certified2074
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
