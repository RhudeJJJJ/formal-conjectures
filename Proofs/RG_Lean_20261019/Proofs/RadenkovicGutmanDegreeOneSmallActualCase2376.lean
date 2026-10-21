/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2376 : Family 10 := level10.get ⟨1147,by decide⟩
def sourceMap2376 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2376 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2376_checked : acceptsGraphIso
    (source (graph core2376) (root 10) 0 0) DegreeOneSmallSpectrum1830.graph sourceMap2376=true := by decide +kernel
theorem fusedMap2376_checked : acceptsGraphIso
    (fused (graph core2376) (root 10) 0 0) DegreeOneSmallSpectrum1829.graph fusedMap2376=true := by decide +kernel
theorem certified2376 : Certified (graph core2376) (root 10) 0 0 :=
  of_native_maps core2376 DegreeOneSmallSpectrum1830.graph DegreeOneSmallSpectrum1829.graph
    sourceMap2376 fusedMap2376 sourceMap2376_checked fusedMap2376_checked
    DegreeOneSmallComparisons.comparison2376
#print axioms sourceMap2376_checked
#print axioms fusedMap2376_checked
#print axioms certified2376
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
