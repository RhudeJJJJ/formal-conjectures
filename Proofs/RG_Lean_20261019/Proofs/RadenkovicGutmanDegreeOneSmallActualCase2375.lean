/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2375 : Family 10 := level10.get ⟨1146,by decide⟩
def sourceMap2375 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2375 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2375_checked : acceptsGraphIso
    (source (graph core2375) (root 10) 0 0) DegreeOneSmallSpectrum1814.graph sourceMap2375=true := by decide +kernel
theorem fusedMap2375_checked : acceptsGraphIso
    (fused (graph core2375) (root 10) 0 0) DegreeOneSmallSpectrum1813.graph fusedMap2375=true := by decide +kernel
theorem certified2375 : Certified (graph core2375) (root 10) 0 0 :=
  of_native_maps core2375 DegreeOneSmallSpectrum1814.graph DegreeOneSmallSpectrum1813.graph
    sourceMap2375 fusedMap2375 sourceMap2375_checked fusedMap2375_checked
    DegreeOneSmallComparisons.comparison2375
#print axioms sourceMap2375_checked
#print axioms fusedMap2375_checked
#print axioms certified2375
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
