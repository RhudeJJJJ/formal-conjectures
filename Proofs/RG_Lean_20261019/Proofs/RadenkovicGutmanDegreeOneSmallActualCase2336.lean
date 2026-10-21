/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2336 : Family 10 := level10.get ⟨1045,by decide⟩
def sourceMap2336 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2336 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2336_checked : acceptsGraphIso
    (source (graph core2336) (root 10) 0 0) DegreeOneSmallSpectrum1639.graph sourceMap2336=true := by decide +kernel
theorem fusedMap2336_checked : acceptsGraphIso
    (fused (graph core2336) (root 10) 0 0) DegreeOneSmallSpectrum1641.graph fusedMap2336=true := by decide +kernel
theorem certified2336 : Certified (graph core2336) (root 10) 0 0 :=
  of_native_maps core2336 DegreeOneSmallSpectrum1639.graph DegreeOneSmallSpectrum1641.graph
    sourceMap2336 fusedMap2336 sourceMap2336_checked fusedMap2336_checked
    DegreeOneSmallComparisons.comparison2336
#print axioms sourceMap2336_checked
#print axioms fusedMap2336_checked
#print axioms certified2336
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
