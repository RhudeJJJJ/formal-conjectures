/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2459 : Family 10 := level10.get ⟨1527,by decide⟩
def sourceMap2459 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2459 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2459_checked : acceptsGraphIso
    (source (graph core2459) (root 10) 0 0) DegreeOneSmallSpectrum1994.graph sourceMap2459=true := by decide +kernel
theorem fusedMap2459_checked : acceptsGraphIso
    (fused (graph core2459) (root 10) 0 0) DegreeOneSmallSpectrum1523.graph fusedMap2459=true := by decide +kernel
theorem certified2459 : Certified (graph core2459) (root 10) 0 0 :=
  of_native_maps core2459 DegreeOneSmallSpectrum1994.graph DegreeOneSmallSpectrum1523.graph
    sourceMap2459 fusedMap2459 sourceMap2459_checked fusedMap2459_checked
    DegreeOneSmallComparisons.comparison2459
#print axioms sourceMap2459_checked
#print axioms fusedMap2459_checked
#print axioms certified2459
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
