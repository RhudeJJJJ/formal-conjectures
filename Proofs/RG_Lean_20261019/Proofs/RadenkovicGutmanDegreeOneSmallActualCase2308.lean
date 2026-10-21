/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2308 : Family 10 := level10.get ⟨958,by decide⟩
def sourceMap2308 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,10,11,12,5,6,7,8,9,3,4] (sourceLabel 10 0 0 v)
def fusedMap2308 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2308_checked : acceptsGraphIso
    (source (graph core2308) (root 10) 0 0) DegreeOneSmallSpectrum1777.graph sourceMap2308=true := by decide +kernel
theorem fusedMap2308_checked : acceptsGraphIso
    (fused (graph core2308) (root 10) 0 0) DegreeOneSmallSpectrum1492.graph fusedMap2308=true := by decide +kernel
theorem certified2308 : Certified (graph core2308) (root 10) 0 0 :=
  of_native_maps core2308 DegreeOneSmallSpectrum1777.graph DegreeOneSmallSpectrum1492.graph
    sourceMap2308 fusedMap2308 sourceMap2308_checked fusedMap2308_checked
    DegreeOneSmallComparisons.comparison2308
#print axioms sourceMap2308_checked
#print axioms fusedMap2308_checked
#print axioms certified2308
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
