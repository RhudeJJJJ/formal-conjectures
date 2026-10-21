/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2425 : Family 10 := level10.get ⟨1318,by decide⟩
def sourceMap2425 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2425 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2425_checked : acceptsGraphIso
    (source (graph core2425) (root 10) 0 0) DegreeOneSmallSpectrum1952.graph sourceMap2425=true := by decide +kernel
theorem fusedMap2425_checked : acceptsGraphIso
    (fused (graph core2425) (root 10) 0 0) DegreeOneSmallSpectrum1950.graph fusedMap2425=true := by decide +kernel
theorem certified2425 : Certified (graph core2425) (root 10) 0 0 :=
  of_native_maps core2425 DegreeOneSmallSpectrum1952.graph DegreeOneSmallSpectrum1950.graph
    sourceMap2425 fusedMap2425 sourceMap2425_checked fusedMap2425_checked
    DegreeOneSmallComparisons.comparison2425
#print axioms sourceMap2425_checked
#print axioms fusedMap2425_checked
#print axioms certified2425
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
