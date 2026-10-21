/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2405 : Family 10 := level10.get ⟨1257,by decide⟩
def sourceMap2405 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2405 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2405_checked : acceptsGraphIso
    (source (graph core2405) (root 10) 0 0) DegreeOneSmallSpectrum1912.graph sourceMap2405=true := by decide +kernel
theorem fusedMap2405_checked : acceptsGraphIso
    (fused (graph core2405) (root 10) 0 0) DegreeOneSmallSpectrum1911.graph fusedMap2405=true := by decide +kernel
theorem certified2405 : Certified (graph core2405) (root 10) 0 0 :=
  of_native_maps core2405 DegreeOneSmallSpectrum1912.graph DegreeOneSmallSpectrum1911.graph
    sourceMap2405 fusedMap2405 sourceMap2405_checked fusedMap2405_checked
    DegreeOneSmallComparisons.comparison2405
#print axioms sourceMap2405_checked
#print axioms fusedMap2405_checked
#print axioms certified2405
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
