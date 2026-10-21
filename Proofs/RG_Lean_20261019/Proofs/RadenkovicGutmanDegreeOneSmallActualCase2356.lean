/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2356 : Family 10 := level10.get ⟨1099,by decide⟩
def sourceMap2356 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2356 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2356_checked : acceptsGraphIso
    (source (graph core2356) (root 10) 0 0) DegreeOneSmallSpectrum1713.graph sourceMap2356=true := by decide +kernel
theorem fusedMap2356_checked : acceptsGraphIso
    (fused (graph core2356) (root 10) 0 0) DegreeOneSmallSpectrum1722.graph fusedMap2356=true := by decide +kernel
theorem certified2356 : Certified (graph core2356) (root 10) 0 0 :=
  of_native_maps core2356 DegreeOneSmallSpectrum1713.graph DegreeOneSmallSpectrum1722.graph
    sourceMap2356 fusedMap2356 sourceMap2356_checked fusedMap2356_checked
    DegreeOneSmallComparisons.comparison2356
#print axioms sourceMap2356_checked
#print axioms fusedMap2356_checked
#print axioms certified2356
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
