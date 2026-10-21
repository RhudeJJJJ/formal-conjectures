/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2449 : Family 10 := level10.get ⟨1425,by decide⟩
def sourceMap2449 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,4,5,6,7,8,9,2,3] (sourceLabel 10 0 0 v)
def fusedMap2449 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2449_checked : acceptsGraphIso
    (source (graph core2449) (root 10) 0 0) DegreeOneSmallSpectrum1697.graph sourceMap2449=true := by decide +kernel
theorem fusedMap2449_checked : acceptsGraphIso
    (fused (graph core2449) (root 10) 0 0) DegreeOneSmallSpectrum1980.graph fusedMap2449=true := by decide +kernel
theorem certified2449 : Certified (graph core2449) (root 10) 0 0 :=
  of_native_maps core2449 DegreeOneSmallSpectrum1697.graph DegreeOneSmallSpectrum1980.graph
    sourceMap2449 fusedMap2449 sourceMap2449_checked fusedMap2449_checked
    DegreeOneSmallComparisons.comparison2449
#print axioms sourceMap2449_checked
#print axioms fusedMap2449_checked
#print axioms certified2449
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
