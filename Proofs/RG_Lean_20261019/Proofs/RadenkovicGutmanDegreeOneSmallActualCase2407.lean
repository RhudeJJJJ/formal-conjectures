/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2407 : Family 10 := level10.get ⟨1259,by decide⟩
def sourceMap2407 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2407 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2407_checked : acceptsGraphIso
    (source (graph core2407) (root 10) 0 0) DegreeOneSmallSpectrum1748.graph sourceMap2407=true := by decide +kernel
theorem fusedMap2407_checked : acceptsGraphIso
    (fused (graph core2407) (root 10) 0 0) DegreeOneSmallSpectrum1913.graph fusedMap2407=true := by decide +kernel
theorem certified2407 : Certified (graph core2407) (root 10) 0 0 :=
  of_native_maps core2407 DegreeOneSmallSpectrum1748.graph DegreeOneSmallSpectrum1913.graph
    sourceMap2407 fusedMap2407 sourceMap2407_checked fusedMap2407_checked
    DegreeOneSmallComparisons.comparison2407
#print axioms sourceMap2407_checked
#print axioms fusedMap2407_checked
#print axioms certified2407
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
