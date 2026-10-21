/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2359 : Family 10 := level10.get ⟨1106,by decide⟩
def sourceMap2359 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2359 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2359_checked : acceptsGraphIso
    (source (graph core2359) (root 10) 0 0) DegreeOneSmallSpectrum1735.graph sourceMap2359=true := by decide +kernel
theorem fusedMap2359_checked : acceptsGraphIso
    (fused (graph core2359) (root 10) 0 0) DegreeOneSmallSpectrum1737.graph fusedMap2359=true := by decide +kernel
theorem certified2359 : Certified (graph core2359) (root 10) 0 0 :=
  of_native_maps core2359 DegreeOneSmallSpectrum1735.graph DegreeOneSmallSpectrum1737.graph
    sourceMap2359 fusedMap2359 sourceMap2359_checked fusedMap2359_checked
    DegreeOneSmallComparisons.comparison2359
#print axioms sourceMap2359_checked
#print axioms fusedMap2359_checked
#print axioms certified2359
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
