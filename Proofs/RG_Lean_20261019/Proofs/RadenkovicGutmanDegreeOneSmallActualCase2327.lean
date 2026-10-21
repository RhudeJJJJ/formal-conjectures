/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2327 : Family 10 := level10.get ⟨1024,by decide⟩
def sourceMap2327 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2327 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2327_checked : acceptsGraphIso
    (source (graph core2327) (root 10) 0 0) DegreeOneSmallSpectrum1589.graph sourceMap2327=true := by decide +kernel
theorem fusedMap2327_checked : acceptsGraphIso
    (fused (graph core2327) (root 10) 0 0) DegreeOneSmallSpectrum1600.graph fusedMap2327=true := by decide +kernel
theorem certified2327 : Certified (graph core2327) (root 10) 0 0 :=
  of_native_maps core2327 DegreeOneSmallSpectrum1589.graph DegreeOneSmallSpectrum1600.graph
    sourceMap2327 fusedMap2327 sourceMap2327_checked fusedMap2327_checked
    DegreeOneSmallComparisons.comparison2327
#print axioms sourceMap2327_checked
#print axioms fusedMap2327_checked
#print axioms certified2327
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
