/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2389 : Family 10 := level10.get ⟨1186,by decide⟩
def sourceMap2389 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2389 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2389_checked : acceptsGraphIso
    (source (graph core2389) (root 10) 0 0) DegreeOneSmallSpectrum1556.graph sourceMap2389=true := by decide +kernel
theorem fusedMap2389_checked : acceptsGraphIso
    (fused (graph core2389) (root 10) 0 0) DegreeOneSmallSpectrum1878.graph fusedMap2389=true := by decide +kernel
theorem certified2389 : Certified (graph core2389) (root 10) 0 0 :=
  of_native_maps core2389 DegreeOneSmallSpectrum1556.graph DegreeOneSmallSpectrum1878.graph
    sourceMap2389 fusedMap2389 sourceMap2389_checked fusedMap2389_checked
    DegreeOneSmallComparisons.comparison2389
#print axioms sourceMap2389_checked
#print axioms fusedMap2389_checked
#print axioms certified2389
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
