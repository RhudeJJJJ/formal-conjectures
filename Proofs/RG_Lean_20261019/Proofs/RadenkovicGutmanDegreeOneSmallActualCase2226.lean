/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2226 : Family 10 := level10.get ⟨764,by decide⟩
def sourceMap2226 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2226 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2226_checked : acceptsGraphIso
    (source (graph core2226) (root 10) 0 0) DegreeOneSmallSpectrum1870.graph sourceMap2226=true := by decide +kernel
theorem fusedMap2226_checked : acceptsGraphIso
    (fused (graph core2226) (root 10) 0 0) DegreeOneSmallSpectrum1395.graph fusedMap2226=true := by decide +kernel
theorem certified2226 : Certified (graph core2226) (root 10) 0 0 :=
  of_native_maps core2226 DegreeOneSmallSpectrum1870.graph DegreeOneSmallSpectrum1395.graph
    sourceMap2226 fusedMap2226 sourceMap2226_checked fusedMap2226_checked
    DegreeOneSmallComparisons.comparison2226
#print axioms sourceMap2226_checked
#print axioms fusedMap2226_checked
#print axioms certified2226
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
