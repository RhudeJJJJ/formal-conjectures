/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2326 : Family 10 := level10.get ⟨1022,by decide⟩
def sourceMap2326 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2326 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2326_checked : acceptsGraphIso
    (source (graph core2326) (root 10) 0 0) DegreeOneSmallSpectrum1587.graph sourceMap2326=true := by decide +kernel
theorem fusedMap2326_checked : acceptsGraphIso
    (fused (graph core2326) (root 10) 0 0) DegreeOneSmallSpectrum1599.graph fusedMap2326=true := by decide +kernel
theorem certified2326 : Certified (graph core2326) (root 10) 0 0 :=
  of_native_maps core2326 DegreeOneSmallSpectrum1587.graph DegreeOneSmallSpectrum1599.graph
    sourceMap2326 fusedMap2326 sourceMap2326_checked fusedMap2326_checked
    DegreeOneSmallComparisons.comparison2326
#print axioms sourceMap2326_checked
#print axioms fusedMap2326_checked
#print axioms certified2326
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
