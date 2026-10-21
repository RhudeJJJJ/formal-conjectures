/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2212 : Family 10 := level10.get ⟨734,by decide⟩
def sourceMap2212 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2212 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2212_checked : acceptsGraphIso
    (source (graph core2212) (root 10) 0 0) DegreeOneSmallSpectrum1803.graph sourceMap2212=true := by decide +kernel
theorem fusedMap2212_checked : acceptsGraphIso
    (fused (graph core2212) (root 10) 0 0) DegreeOneSmallSpectrum1362.graph fusedMap2212=true := by decide +kernel
theorem certified2212 : Certified (graph core2212) (root 10) 0 0 :=
  of_native_maps core2212 DegreeOneSmallSpectrum1803.graph DegreeOneSmallSpectrum1362.graph
    sourceMap2212 fusedMap2212 sourceMap2212_checked fusedMap2212_checked
    DegreeOneSmallComparisons.comparison2212
#print axioms sourceMap2212_checked
#print axioms fusedMap2212_checked
#print axioms certified2212
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
