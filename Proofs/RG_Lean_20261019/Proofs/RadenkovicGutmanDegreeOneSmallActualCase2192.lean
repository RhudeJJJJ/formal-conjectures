/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2192 : Family 10 := level10.get ⟨696,by decide⟩
def sourceMap2192 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2192 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2192_checked : acceptsGraphIso
    (source (graph core2192) (root 10) 0 0) DegreeOneSmallSpectrum1800.graph sourceMap2192=true := by decide +kernel
theorem fusedMap2192_checked : acceptsGraphIso
    (fused (graph core2192) (root 10) 0 0) DegreeOneSmallSpectrum1311.graph fusedMap2192=true := by decide +kernel
theorem certified2192 : Certified (graph core2192) (root 10) 0 0 :=
  of_native_maps core2192 DegreeOneSmallSpectrum1800.graph DegreeOneSmallSpectrum1311.graph
    sourceMap2192 fusedMap2192 sourceMap2192_checked fusedMap2192_checked
    DegreeOneSmallComparisons.comparison2192
#print axioms sourceMap2192_checked
#print axioms fusedMap2192_checked
#print axioms certified2192
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
