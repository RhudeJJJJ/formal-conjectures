/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2031 : Family 10 := level10.get ⟨383,by decide⟩
def sourceMap2031 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2031 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2031_checked : acceptsGraphIso
    (source (graph core2031) (root 10) 0 0) DegreeOneSmallSpectrum1155.graph sourceMap2031=true := by decide +kernel
theorem fusedMap2031_checked : acceptsGraphIso
    (fused (graph core2031) (root 10) 0 0) DegreeOneSmallSpectrum1489.graph fusedMap2031=true := by decide +kernel
theorem certified2031 : Certified (graph core2031) (root 10) 0 0 :=
  of_native_maps core2031 DegreeOneSmallSpectrum1155.graph DegreeOneSmallSpectrum1489.graph
    sourceMap2031 fusedMap2031 sourceMap2031_checked fusedMap2031_checked
    DegreeOneSmallComparisons.comparison2031
#print axioms sourceMap2031_checked
#print axioms fusedMap2031_checked
#print axioms certified2031
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
