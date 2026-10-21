/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2379 : Family 10 := level10.get ⟨1151,by decide⟩
def sourceMap2379 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2379 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2379_checked : acceptsGraphIso
    (source (graph core2379) (root 10) 0 0) DegreeOneSmallSpectrum1706.graph sourceMap2379=true := by decide +kernel
theorem fusedMap2379_checked : acceptsGraphIso
    (fused (graph core2379) (root 10) 0 0) DegreeOneSmallSpectrum1835.graph fusedMap2379=true := by decide +kernel
theorem certified2379 : Certified (graph core2379) (root 10) 0 0 :=
  of_native_maps core2379 DegreeOneSmallSpectrum1706.graph DegreeOneSmallSpectrum1835.graph
    sourceMap2379 fusedMap2379 sourceMap2379_checked fusedMap2379_checked
    DegreeOneSmallComparisons.comparison2379
#print axioms sourceMap2379_checked
#print axioms fusedMap2379_checked
#print axioms certified2379
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
