/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2322 : Family 10 := level10.get ⟨1015,by decide⟩
def sourceMap2322 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2322 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2322_checked : acceptsGraphIso
    (source (graph core2322) (root 10) 0 0) DegreeOneSmallSpectrum1578.graph sourceMap2322=true := by decide +kernel
theorem fusedMap2322_checked : acceptsGraphIso
    (fused (graph core2322) (root 10) 0 0) DegreeOneSmallSpectrum1584.graph fusedMap2322=true := by decide +kernel
theorem certified2322 : Certified (graph core2322) (root 10) 0 0 :=
  of_native_maps core2322 DegreeOneSmallSpectrum1578.graph DegreeOneSmallSpectrum1584.graph
    sourceMap2322 fusedMap2322 sourceMap2322_checked fusedMap2322_checked
    DegreeOneSmallComparisons.comparison2322
#print axioms sourceMap2322_checked
#print axioms fusedMap2322_checked
#print axioms certified2322
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
