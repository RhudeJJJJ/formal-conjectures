/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2430 : Family 10 := level10.get ⟨1328,by decide⟩
def sourceMap2430 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2430 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2430_checked : acceptsGraphIso
    (source (graph core2430) (root 10) 0 0) DegreeOneSmallSpectrum1781.graph sourceMap2430=true := by decide +kernel
theorem fusedMap2430_checked : acceptsGraphIso
    (fused (graph core2430) (root 10) 0 0) DegreeOneSmallSpectrum1955.graph fusedMap2430=true := by decide +kernel
theorem certified2430 : Certified (graph core2430) (root 10) 0 0 :=
  of_native_maps core2430 DegreeOneSmallSpectrum1781.graph DegreeOneSmallSpectrum1955.graph
    sourceMap2430 fusedMap2430 sourceMap2430_checked fusedMap2430_checked
    DegreeOneSmallComparisons.comparison2430
#print axioms sourceMap2430_checked
#print axioms fusedMap2430_checked
#print axioms certified2430
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
